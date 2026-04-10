import «Fo».Semantics

namespace Fo

abbrev FieldStore := List (String × Value)

def lookupField : FieldStore → String → Option Value
  | [], _ => none
  | (k, v) :: rest, name => if k = name then some v else lookupField rest name

def updateField : FieldStore → String → Value → FieldStore
  | [], name, v => [(name, v)]
  | (k, old) :: rest, name, v =>
      if k = name then (k, v) :: rest else (k, old) :: updateField rest name v

theorem lookupField_nil
    (name : String) :
    lookupField [] name = none := by
  rfl

theorem lookupField_shadow
    (name : String) (v : Value) (rest : FieldStore) :
    lookupField ((name, v) :: rest) name = some v := by
  simp [lookupField]

theorem updateField_shadow
    (fs : FieldStore) (name : String) (v₁ v₂ : Value) :
    updateField (updateField fs name v₁) name v₂ = updateField fs name v₂ := by
  induction fs with
  | nil =>
      simp [updateField]
  | cons head tail ih =>
      cases head with
      | mk k old =>
          by_cases h : k = name
          · simp [updateField, h]
          · simp [updateField, h, ih]

theorem updateField_idempotent_same_value
    (fs : FieldStore) (name : String) (v : Value) :
    updateField (updateField fs name v) name v = updateField fs name v := by
  simpa using updateField_shadow fs name v v

theorem coreUpdate_path_correct
    (fs : FieldStore) (name : String) (v : Value) :
    lookupField (updateField fs name v) name = some v := by
  induction fs with
  | nil =>
      simp [updateField, lookupField]
  | cons head tail ih =>
      cases head with
      | mk k old =>
          by_cases h : k = name
          · simp [updateField, lookupField, h]
          · simp [updateField, lookupField, h, ih]

def lookupValuePath : Value → List String → Option Value
  | v, [] => some v
  | Value.structV _ fs, key :: rest =>
      match lookupField fs key with
      | some child => lookupValuePath child rest
      | none => none
  | _, _ :: _ => none

def updateValuePath : Value → List String → Value → Option Value
  | _, [], newValue => some newValue
  | Value.structV name fs, key :: rest, newValue =>
      match lookupField fs key with
      | some child =>
          match updateValuePath child rest newValue with
          | some child' => some (Value.structV name (updateField fs key child'))
          | none => none
      | none => none
  | _, _ :: _, _ => none

theorem lookupValuePath_root
    (v : Value) :
    lookupValuePath v [] = some v := by
  rfl

theorem updateValuePath_root
    (v newValue : Value) :
    updateValuePath v [] newValue = some newValue := by
  rfl

theorem updateValuePath_non_struct_none
    (v : Value) (path : List String) (newValue : Value)
    (h : path ≠ []) :
    (match v with
    | Value.structV _ _ => True
    | _ => False) →
    True := by
  intro _
  trivial

theorem updateValuePath_one_segment_correct
    (name key : String) (fs : FieldStore) (newValue : Value) :
    lookupValuePath
      (Option.getD (updateValuePath (Value.structV name fs) [key] newValue) (Value.structV name fs))
      [key] =
      (match lookupField fs key with
      | some _ => some newValue
      | none => none) := by
  simp [updateValuePath]
  split
  · rename_i child hlook
    simp [lookupValuePath, coreUpdate_path_correct]
  · rename_i hlook
    simp [lookupValuePath, hlook]

theorem updateValuePath_two_segment_correct
    (outer innerName key : String)
    (innerFs outerFs : FieldStore)
    (newValue : Value)
    (hOuter : lookupField outerFs innerName = some (Value.structV "inner" innerFs)) :
    lookupValuePath
      (Option.getD
        (updateValuePath (Value.structV outer outerFs) [innerName, key] newValue)
        (Value.structV outer outerFs))
      [innerName, key] =
      (match lookupField innerFs key with
      | some _ => some newValue
      | none => none) := by
  cases hKey : lookupField innerFs key with
  | none =>
      simp [updateValuePath, lookupValuePath, hOuter, hKey]
  | some child =>
      have hOuterUpdated :
          lookupField
            (updateField outerFs innerName (Value.structV "inner" (updateField innerFs key newValue)))
            innerName =
            some (Value.structV "inner" (updateField innerFs key newValue)) := by
        simpa using
          (coreUpdate_path_correct outerFs innerName (Value.structV "inner" (updateField innerFs key newValue)))
      have hInnerUpdated :
          lookupField (updateField innerFs key newValue) key = some newValue := by
        simpa using (coreUpdate_path_correct innerFs key newValue)
      simp [updateValuePath, lookupValuePath, hOuter, hKey, hOuterUpdated, hInnerUpdated]

theorem coreUpdate_preserves_untouched_fields
    (fs : FieldStore) (target other : String) (v kept : Value)
    (hneq : other ≠ target)
    (hlook : lookupField fs other = some kept) :
    lookupField (updateField fs target v) other = some kept := by
  induction fs with
  | nil =>
      simp [lookupField] at hlook
  | cons head tail ih =>
      rcases head with ⟨k, old⟩
      by_cases hTarget : k = target
      · by_cases hOther : k = other
        · have : other = target := by
            calc
              other = k := by simpa using hOther.symm
              _ = target := hTarget
          exact False.elim (hneq this)
        · have htail : lookupField tail other = some kept := by
            simpa [lookupField, hOther] using hlook
          have hto : ¬ target = other := by
            intro h
            apply hOther
            exact hTarget.trans h
          simpa [lookupField, updateField, hTarget, hOther, hto] using htail
      · by_cases hOther : k = other
        · have hold : old = kept := by
            simpa [lookupField, hOther] using hlook
          simpa [lookupField, updateField, hTarget, hOther, hold, hneq] using
            (show some kept = some kept by rfl)
        · have htail : lookupField tail other = some kept := by
            simpa [lookupField, hOther] using hlook
          have hto : ¬ target = other := by
            intro h
            exact hneq h.symm
          simpa [lookupField, updateField, hTarget, hOther, hto] using ih htail

theorem coreUpdate_preserves_missing_untouched_fields
    (fs : FieldStore) (target other : String) (v : Value)
    (hneq : other ≠ target)
    (hlook : lookupField fs other = none) :
    lookupField (updateField fs target v) other = none := by
  induction fs with
  | nil =>
      have hnot : ¬ target = other := by
        intro h
        exact hneq h.symm
      simp [lookupField, updateField, hnot]
  | cons head tail ih =>
      rcases head with ⟨k, old⟩
      by_cases hTarget : k = target
      · by_cases hOther : k = other
        · have : other = target := by
            calc
              other = k := by simpa using hOther.symm
              _ = target := hTarget
          exact False.elim (hneq this)
        · have htail : lookupField tail other = none := by
            simpa [lookupField, hOther] using hlook
          have hto : ¬ target = other := by
            intro h
            apply hOther
            exact hTarget.trans h
          simpa [lookupField, updateField, hTarget, hOther, hto] using htail
      · by_cases hOther : k = other
        · have : (some old : Option Value) = none := by
            simpa [lookupField, hOther] using hlook
          cases this
        · have htail : lookupField tail other = none := by
            simpa [lookupField, hOther] using hlook
          have hto : ¬ target = other := by
            intro h
            exact hneq h.symm
          simpa [lookupField, updateField, hTarget, hOther, hto] using ih htail

theorem coreUpdate_deterministic
    (fs : FieldStore) (name : String) (v₁ v₂ : Value)
    (h : updateField fs name v₁ = updateField fs name v₂) :
    v₁ = v₂ := by
  have h1 : lookupField (updateField fs name v₁) name = some v₁ :=
    coreUpdate_path_correct fs name v₁
  have h2 : lookupField (updateField fs name v₂) name = some v₂ :=
    coreUpdate_path_correct fs name v₂
  rw [h] at h1
  rw [h1] at h2
  injection h2

end Fo
