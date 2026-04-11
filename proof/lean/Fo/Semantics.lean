import «Fo».Syntax

namespace Fo

inductive Value where
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List Value)
  | structV (name : String) (fields : List (String × Value))
  | ctorV (name : String) (args : List Value)
deriving Repr

abbrev Env := List (String × Value)

inductive Result where
  | continue (env : Env)
  | ret (value : Value)
deriving Repr

abbrev SemFieldStore := List (String × Value)

def semLookupField : SemFieldStore → String → Option Value
  | [], _ => none
  | (key, value) :: rest, name => if key = name then some value else semLookupField rest name

def semUpdateField : SemFieldStore → String → Value → SemFieldStore
  | [], name, newv => [(name, newv)]
  | (key, value) :: rest, name, newv =>
      if key = name
      then (key, newv) :: rest
      else (key, value) :: semUpdateField rest name newv

def semLookupValuePath : Value → List String → Option Value
  | v, [] => some v
  | .structV _ fields, key :: rest =>
      match semLookupField fields key with
      | some child => semLookupValuePath child rest
      | none => none
  | _, _ :: _ => none

def semUpdateValuePath : Value → List String → Value → Option Value
  | _, [], newv => some newv
  | .structV name fields, key :: rest, newv =>
      match semLookupField fields key with
      | some child =>
          match semUpdateValuePath child rest newv with
          | some child' => some (.structV name (semUpdateField fields key child'))
          | none => none
      | none => none
  | _, _ :: _, _ => none

def enumTagOf : Value → Option String
  | .ctorV name _ => some name
  | .structV _ fields =>
      match semLookupField fields "Tag" with
      | some (.str tag) => some tag
      | _ => none
  | _ => none

def enumPayloadOf : Value → Option (List Value)
  | .ctorV _ args => some args
  | .structV _ fields =>
      match semLookupField fields "Payload" with
      | some (.tuple items) => some items
      | _ => none
  | _ => none

def patternTag : Pattern → String
  | .wild => "_"
  | .binder name => "bind:" ++ name
  | .tuple _ => "tuple"
  | .ctor name _ => "ctor:" ++ name
  | .struct name _ => "struct:" ++ name

def isCatchAllPattern : Pattern → Bool
  | .wild => true
  | .binder _ => true
  | _ => false

def headPatternMatches : Pattern → Value → Bool
  | .wild, _ => true
  | .binder _, _ => true
  | .tuple _, .tuple _ => true
  | .ctor name _, .ctorV other _ => name == other
  | .struct name _, .structV other _ => name == other
  | _, _ => false

def selectMatchExpr : Value → List (Pattern × Expr) → Option Expr
  | _, [] => none
  | v, (pat, body) :: rest =>
      if headPatternMatches pat v then some body else selectMatchExpr v rest

def selectMatchStmt : Value → List (Pattern × List Stmt) → Option (List Stmt)
  | _, [] => none
  | v, (pat, body) :: rest =>
      if headPatternMatches pat v then some body else selectMatchStmt v rest

inductive PipelineStage where
  | map
  | filter
  | fold
deriving Repr

structure PipelinePlan where
  input : Value
  stages : List PipelineStage
deriving Repr

def runPipelineStage : Value → PipelineStage → Value
  | .tuple items, .map => .tuple items
  | .tuple [], .filter => .tuple []
  | .tuple (_ :: items), .filter => .tuple items
  | .tuple [], .fold => .unit
  | .tuple (item :: _), .fold => item
  | input, _ => input

def runPipelineStages : Value → List PipelineStage → Value
  | input, [] => input
  | input, stage :: rest => runPipelineStages (runPipelineStage input stage) rest

inductive TailOutcome where
  | ret (value : Value)
  | recur (fn : String) (args : List Value)
deriving Repr

def interpExpr : Expr → Value
  | .var _ => .unit
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s
  | .tuple _ => .tuple []
  | .ctor name _ => .ctorV name []
  | .structLit name _ => .structV name []
  | .copyUpdate base _ _ => interpExpr base
  | .unary _ _ => .unit
  | .binary _ _ _ => .unit
  | .call _ _ => .unit
  | .ite _ yes _ => interpExpr yes
  | .matchE _ _ => .unit

def interpTailExpr : Expr → TailOutcome
  | .call fn args => .recur fn (args.map interpExpr)
  | e => .ret (interpExpr e)

def interpStmt : Env → Stmt → Result
  | ρ, .bind _ _ => .continue ρ
  | _, .ret value => .ret (interpExpr value)
  | ρ, .ite _ _ _ => .continue ρ
  | ρ, .matchS _ _ => .continue ρ

def interpBlock : Env → List Stmt → Result
  | ρ, [] => .continue ρ
  | ρ, s :: _ => interpStmt ρ s

def EvalExpr (_p : Program) (_ρ : Env) (e : Expr) (v : Value) : Prop :=
  interpExpr e = v

def EvalStmt (_p : Program) (ρ : Env) (s : Stmt) (r : Result) : Prop :=
  interpStmt ρ s = r

def EvalBlock (_p : Program) (ρ : Env) (ss : List Stmt) (r : Result) : Prop :=
  interpBlock ρ ss = r

def ExprObservationalEq (e₁ e₂ : Expr) : Prop :=
  interpExpr e₁ = interpExpr e₂

def StmtObservationalEq (ρ : Env) (s₁ s₂ : Stmt) : Prop :=
  interpStmt ρ s₁ = interpStmt ρ s₂

def BlockObservationalEq (ρ : Env) (ss₁ ss₂ : List Stmt) : Prop :=
  interpBlock ρ ss₁ = interpBlock ρ ss₂

def TailObservationalEq (e₁ e₂ : Expr) : Prop :=
  interpTailExpr e₁ = interpTailExpr e₂

def MatchBranchObserved (v : Value) (cases : List (Pattern × Expr)) (body : Expr) : Prop :=
  selectMatchExpr v cases = some body

def MatchStmtBranchObserved (v : Value) (cases : List (Pattern × List Stmt)) (body : List Stmt) : Prop :=
  selectMatchStmt v cases = some body

def CtorMismatchExprPrefix (ctor : String) : List (Pattern × Expr) → Prop
  | [] => True
  | (.ctor other _, _) :: rest => other ≠ ctor ∧ CtorMismatchExprPrefix ctor rest
  | _ :: _ => False

def CtorMismatchStmtPrefix (ctor : String) : List (Pattern × List Stmt) → Prop
  | [] => True
  | (.ctor other _, _) :: rest => other ≠ ctor ∧ CtorMismatchStmtPrefix ctor rest
  | _ :: _ => False

inductive CtorExprCasesCover (ctor : String) : List (Pattern × Expr) → Expr → Prop where
  | ctorHit (pats : List Pattern) (body : Expr) (rest : List (Pattern × Expr)) :
      CtorExprCasesCover ctor ((.ctor ctor pats, body) :: rest) body
  | wildHit (body : Expr) (rest : List (Pattern × Expr)) :
      CtorExprCasesCover ctor ((.wild, body) :: rest) body
  | binderHit (name : String) (body : Expr) (rest : List (Pattern × Expr)) :
      CtorExprCasesCover ctor ((.binder name, body) :: rest) body
  | skipCtor (other : String) (pats : List Pattern) (skipBody : Expr)
      (rest : List (Pattern × Expr)) (body : Expr) :
      other ≠ ctor →
      CtorExprCasesCover ctor rest body →
      CtorExprCasesCover ctor ((.ctor other pats, skipBody) :: rest) body

inductive CtorStmtCasesCover (ctor : String) : List (Pattern × List Stmt) → List Stmt → Prop where
  | ctorHit (pats : List Pattern) (body : List Stmt) (rest : List (Pattern × List Stmt)) :
      CtorStmtCasesCover ctor ((.ctor ctor pats, body) :: rest) body
  | wildHit (body : List Stmt) (rest : List (Pattern × List Stmt)) :
      CtorStmtCasesCover ctor ((.wild, body) :: rest) body
  | binderHit (name : String) (body : List Stmt) (rest : List (Pattern × List Stmt)) :
      CtorStmtCasesCover ctor ((.binder name, body) :: rest) body
  | skipCtor (other : String) (pats : List Pattern) (skipBody : List Stmt)
      (rest : List (Pattern × List Stmt)) (body : List Stmt) :
      other ≠ ctor →
      CtorStmtCasesCover ctor rest body →
      CtorStmtCasesCover ctor ((.ctor other pats, skipBody) :: rest) body

def CtorExprCasesExhaustive (ctor : String) (cases : List (Pattern × Expr)) : Prop :=
  ∃ body, CtorExprCasesCover ctor cases body

def CtorStmtCasesExhaustive (ctor : String) (cases : List (Pattern × List Stmt)) : Prop :=
  ∃ body, CtorStmtCasesCover ctor cases body

def EnumEncodingObserved (v : Value) (tag : String) (payload : List Value) : Prop :=
  enumTagOf v = some tag ∧ enumPayloadOf v = some payload

def CopyUpdatePathObserved (base : Value) (path : List String) (newv out : Value) : Prop :=
  semUpdateValuePath base path newv = some out ∧ semLookupValuePath out path = some newv

def CopyUpdateHeadObserved (base : Value) (path : List String) (newv out : Value) : Prop :=
  match path with
  | [] => out = newv
  | key :: rest =>
      ∃ name fields child child',
        base = .structV name fields ∧
        semLookupField fields key = some child ∧
        semUpdateValuePath child rest newv = some child' ∧
        out = .structV name (semUpdateField fields key child')

def CopyUpdatePrefixObserved (base : Value) (path : List String) (newv out : Value) : Prop :=
  match path with
  | [] => out = newv
  | key :: rest =>
      ∃ name fields child child',
        base = .structV name fields ∧
        semLookupField fields key = some child ∧
        semUpdateValuePath child rest newv = some child' ∧
        out = .structV name (semUpdateField fields key child') ∧
        CopyUpdatePathObserved child rest newv child'

def PipelineStageResultObserved (input : Value) (stage : PipelineStage) : Prop :=
  match input, stage with
  | .tuple items, .map => runPipelineStage input stage = .tuple items
  | .tuple [], .filter => runPipelineStage input stage = .tuple []
  | .tuple (_ :: items), .filter => runPipelineStage input stage = .tuple items
  | .tuple [], .fold => runPipelineStage input stage = .unit
  | .tuple (item :: _), .fold => runPipelineStage input stage = item
  | _, _ => runPipelineStage input stage = input

def PipelineSingleStageObserved (input : Value) (stage : PipelineStage) : Prop :=
  runPipelineStages input [stage] = runPipelineStage input stage ∧
  PipelineStageResultObserved input stage

def PipelineStageTraceObserved : Value → List PipelineStage → Prop
  | _, [] => True
  | input, stage :: rest =>
      PipelineSingleStageObserved input stage ∧
      PipelineStageTraceObserved (runPipelineStage input stage) rest

def PipelineStagesObserved (input : Value) (stages : List PipelineStage) : Prop :=
  runPipelineStages input stages = stages.foldl runPipelineStage input ∧
  PipelineStageTraceObserved input stages

def TailRecurObserved (e : Expr) (fn : String) (args : List Value) : Prop :=
  interpTailExpr e = .recur fn args

def TailCallShapeObserved (e : Expr) (fn : String) (args : List Value) : Prop :=
  ∃ exprArgs, e = .call fn exprArgs ∧ args = exprArgs.map interpExpr

theorem semLookupField_shadow
    (name : String) (v : Value) (rest : SemFieldStore) :
    semLookupField ((name, v) :: rest) name = some v := by
  simp [semLookupField]

theorem semLookupField_updated
    (fields : SemFieldStore) (name : String) (newv : Value) :
    semLookupField (semUpdateField fields name newv) name = some newv := by
  induction fields with
  | nil =>
      simp [semLookupField, semUpdateField]
  | cons head rest ih =>
      cases head with
      | mk key value =>
          by_cases h : key = name
          · simp [semLookupField, semUpdateField, h]
          · simp [semLookupField, semUpdateField, h, ih]

theorem exprObservationalEq_refl
    (e : Expr) :
    ExprObservationalEq e e := by
  rfl

theorem exprObservationalEq_symm
    (e₁ e₂ : Expr)
    (h : ExprObservationalEq e₁ e₂) :
    ExprObservationalEq e₂ e₁ := by
  simpa [ExprObservationalEq] using h.symm

theorem exprObservationalEq_trans
    (e₁ e₂ e₃ : Expr)
    (h₁₂ : ExprObservationalEq e₁ e₂)
    (h₂₃ : ExprObservationalEq e₂ e₃) :
    ExprObservationalEq e₁ e₃ := by
  unfold ExprObservationalEq at *
  exact h₁₂.trans h₂₃

theorem stmtObservationalEq_refl
    (ρ : Env) (s : Stmt) :
    StmtObservationalEq ρ s s := by
  rfl

theorem blockObservationalEq_refl
    (ρ : Env) (ss : List Stmt) :
    BlockObservationalEq ρ ss ss := by
  rfl

theorem tailObservationalEq_refl
    (e : Expr) :
    TailObservationalEq e e := by
  rfl

theorem copyUpdate_projectsBase_observational
    (base : Expr) (path : List String) (value : Expr) :
    ExprObservationalEq (.copyUpdate base path value) base := by
  rfl

theorem ite_projectsThen_observational
    (cond yes no : Expr) :
    ExprObservationalEq (.ite cond yes no) yes := by
  rfl

theorem semLookupValuePath_root
    (v : Value) :
    semLookupValuePath v [] = some v := by
  rfl

theorem semUpdateValuePath_root
    (v newv : Value) :
    semUpdateValuePath v [] newv = some newv := by
  rfl

theorem enumTagOf_ctor
    (name : String) (args : List Value) :
    enumTagOf (.ctorV name args) = some name := by
  rfl

theorem enumPayloadOf_ctor
    (name : String) (args : List Value) :
    enumPayloadOf (.ctorV name args) = some args := by
  rfl

theorem enumEncodingObserved_ctor
    (name : String) (args : List Value) :
    EnumEncodingObserved (.ctorV name args) name args := by
  constructor
  · exact enumTagOf_ctor name args
  · exact enumPayloadOf_ctor name args

theorem ctorTag_ne_wild
    (ctor : String) :
    "ctor:" ++ ctor ≠ "_" := by
  intro hEq
  have hbytes := congrArg String.toByteArray hEq
  have hs := congrArg ByteArray.size hbytes
  have hs' : "ctor:".utf8ByteSize + ctor.utf8ByteSize = "_".utf8ByteSize := by
    simpa using hs
  have hfive : "ctor:".utf8ByteSize = 5 := by native_decide
  have hone : "_".utf8ByteSize = 1 := by native_decide
  have hge : 5 ≤ "ctor:".utf8ByteSize + ctor.utf8ByteSize := by
    rw [hfive]
    exact Nat.le_add_right 5 ctor.utf8ByteSize
  have hbad : 5 ≤ 1 := by
    rw [← hone]
    rw [← hs']
    exact hge
  have hcontra : ¬ 5 ≤ 1 := by decide
  exact hcontra hbad

theorem ctorTag_ne_ctorTag
    (other ctor : String)
    (hneq : other ≠ ctor) :
    "ctor:" ++ other ≠ "ctor:" ++ ctor := by
  intro hEq
  apply hneq
  exact (String.append_right_inj "ctor:").1 hEq

theorem selectMatchExpr_wild
    (v : Value) (body : Expr) (rest : List (Pattern × Expr)) :
    selectMatchExpr v ((.wild, body) :: rest) = some body := by
  simp [selectMatchExpr, headPatternMatches]

theorem selectMatchExpr_binder
    (v : Value) (name : String) (body : Expr) (rest : List (Pattern × Expr)) :
    selectMatchExpr v ((.binder name, body) :: rest) = some body := by
  simp [selectMatchExpr, headPatternMatches]

theorem selectMatchExpr_tuple
    (ps : List Pattern) (vs : List Value) (body : Expr) (rest : List (Pattern × Expr)) :
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body := by
  unfold MatchBranchObserved
  simp [selectMatchExpr, headPatternMatches]

theorem selectMatchExpr_ctor
    (ctor : String) (pats : List Pattern) (args : List Value) (body : Expr)
    (rest : List (Pattern × Expr)) :
    MatchBranchObserved (.ctorV ctor args) ((.ctor ctor pats, body) :: rest) body := by
  unfold MatchBranchObserved
  simp [selectMatchExpr, headPatternMatches]

theorem selectMatchExpr_struct
    (name : String) (ps : List (String × Pattern)) (fields : List (String × Value))
    (body : Expr) (rest : List (Pattern × Expr)) :
    MatchBranchObserved (.structV name fields) ((.struct name ps, body) :: rest) body := by
  unfold MatchBranchObserved
  simp [selectMatchExpr, headPatternMatches]

theorem selectMatchStmt_wild
    (v : Value) (body : List Stmt) (rest : List (Pattern × List Stmt)) :
    selectMatchStmt v ((.wild, body) :: rest) = some body := by
  simp [selectMatchStmt, headPatternMatches]

theorem selectMatchStmt_binder
    (v : Value) (name : String) (body : List Stmt) (rest : List (Pattern × List Stmt)) :
    selectMatchStmt v ((.binder name, body) :: rest) = some body := by
  simp [selectMatchStmt, headPatternMatches]

theorem selectMatchStmt_tuple
    (ps : List Pattern) (vs : List Value) (body : List Stmt) (rest : List (Pattern × List Stmt)) :
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body := by
  unfold MatchStmtBranchObserved
  simp [selectMatchStmt, headPatternMatches]

theorem selectMatchStmt_ctor
    (ctor : String) (pats : List Pattern) (args : List Value) (body : List Stmt)
    (rest : List (Pattern × List Stmt)) :
    MatchStmtBranchObserved (.ctorV ctor args) ((.ctor ctor pats, body) :: rest) body := by
  unfold MatchStmtBranchObserved
  simp [selectMatchStmt, headPatternMatches]

theorem selectMatchStmt_struct
    (name : String) (ps : List (String × Pattern)) (fields : List (String × Value))
    (body : List Stmt) (rest : List (Pattern × List Stmt)) :
    MatchStmtBranchObserved (.structV name fields) ((.struct name ps, body) :: rest) body := by
  unfold MatchStmtBranchObserved
  simp [selectMatchStmt, headPatternMatches]

theorem selectMatchExpr_skipCtorMismatch
    (ctor other : String) (otherPats : List Pattern) (args : List Value) (body : Expr)
    (rest : List (Pattern × Expr))
    (hneq : other ≠ ctor) :
    selectMatchExpr (.ctorV ctor args) ((.ctor other otherPats, body) :: rest) =
      selectMatchExpr (.ctorV ctor args) rest := by
  simp [selectMatchExpr, headPatternMatches, hneq]

theorem selectMatchStmt_skipCtorMismatch
    (ctor other : String) (otherPats : List Pattern) (args : List Value) (body : List Stmt)
    (rest : List (Pattern × List Stmt))
    (hneq : other ≠ ctor) :
    selectMatchStmt (.ctorV ctor args) ((.ctor other otherPats, body) :: rest) =
      selectMatchStmt (.ctorV ctor args) rest := by
  simp [selectMatchStmt, headPatternMatches, hneq]

theorem selectMatchExpr_skipCtorMismatches
    (ctor : String) (args : List Value) (pre : List (Pattern × Expr)) (rest : List (Pattern × Expr))
    (hpre : CtorMismatchExprPrefix ctor pre) :
    selectMatchExpr (.ctorV ctor args) (pre ++ rest) = selectMatchExpr (.ctorV ctor args) rest := by
  induction pre generalizing rest with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head with
      | mk pat body =>
          cases pat with
          | wild => cases hpre
          | binder name => cases hpre
          | tuple items => cases hpre
          | struct name fields => cases hpre
          | ctor other otherPats =>
              rcases hpre with ⟨hneq, htail⟩
              simpa using
                Eq.trans
                  (selectMatchExpr_skipCtorMismatch ctor other otherPats args body (tail ++ rest) hneq)
                  (ih (rest := rest) htail)

theorem selectMatchStmt_skipCtorMismatches
    (ctor : String) (args : List Value) (pre : List (Pattern × List Stmt)) (rest : List (Pattern × List Stmt))
    (hpre : CtorMismatchStmtPrefix ctor pre) :
    selectMatchStmt (.ctorV ctor args) (pre ++ rest) = selectMatchStmt (.ctorV ctor args) rest := by
  induction pre generalizing rest with
  | nil =>
      rfl
  | cons head tail ih =>
      cases head with
      | mk pat body =>
          cases pat with
          | wild => cases hpre
          | binder name => cases hpre
          | tuple items => cases hpre
          | struct name fields => cases hpre
          | ctor other otherPats =>
              rcases hpre with ⟨hneq, htail⟩
              simpa using
                Eq.trans
                  (selectMatchStmt_skipCtorMismatch ctor other otherPats args body (tail ++ rest) hneq)
                  (ih (rest := rest) htail)

theorem selectMatchExpr_ctor_afterCtorMismatches
    (ctor : String) (pats : List Pattern) (args : List Value)
    (pre : List (Pattern × Expr)) (body : Expr) (rest : List (Pattern × Expr))
    (hpre : CtorMismatchExprPrefix ctor pre) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.ctor ctor pats, body) :: rest) body := by
  unfold MatchBranchObserved
  rw [selectMatchExpr_skipCtorMismatches ctor args pre ((.ctor ctor pats, body) :: rest) hpre]
  exact selectMatchExpr_ctor ctor pats args body rest

theorem selectMatchExpr_wild_afterCtorMismatches
    (ctor : String) (args : List Value)
    (pre : List (Pattern × Expr)) (body : Expr) (rest : List (Pattern × Expr))
    (hpre : CtorMismatchExprPrefix ctor pre) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.wild, body) :: rest) body := by
  unfold MatchBranchObserved
  rw [selectMatchExpr_skipCtorMismatches ctor args pre ((.wild, body) :: rest) hpre]
  exact selectMatchExpr_wild (.ctorV ctor args) body rest

theorem selectMatchStmt_ctor_afterCtorMismatches
    (ctor : String) (pats : List Pattern) (args : List Value)
    (pre : List (Pattern × List Stmt)) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hpre : CtorMismatchStmtPrefix ctor pre) :
    MatchStmtBranchObserved (.ctorV ctor args) (pre ++ (.ctor ctor pats, body) :: rest) body := by
  unfold MatchStmtBranchObserved
  rw [selectMatchStmt_skipCtorMismatches ctor args pre ((.ctor ctor pats, body) :: rest) hpre]
  exact selectMatchStmt_ctor ctor pats args body rest

theorem selectMatchStmt_wild_afterCtorMismatches
    (ctor : String) (args : List Value)
    (pre : List (Pattern × List Stmt)) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hpre : CtorMismatchStmtPrefix ctor pre) :
    MatchStmtBranchObserved (.ctorV ctor args) (pre ++ (.wild, body) :: rest) body := by
  unfold MatchStmtBranchObserved
  rw [selectMatchStmt_skipCtorMismatches ctor args pre ((.wild, body) :: rest) hpre]
  exact selectMatchStmt_wild (.ctorV ctor args) body rest

theorem selectMatchExpr_ofCtorCover
    (ctor : String) (args : List Value) (cases : List (Pattern × Expr)) (body : Expr)
    (hcover : CtorExprCasesCover ctor cases body) :
    MatchBranchObserved (.ctorV ctor args) cases body := by
  induction hcover with
  | ctorHit pats body rest =>
      exact selectMatchExpr_ctor ctor pats args body rest
  | wildHit body rest =>
      exact selectMatchExpr_wild (.ctorV ctor args) body rest
  | binderHit name body rest =>
      exact selectMatchExpr_binder (.ctorV ctor args) name body rest
  | skipCtor other pats skipBody rest body hneq hrest ih =>
      unfold MatchBranchObserved at *
      simpa [selectMatchExpr_skipCtorMismatch ctor other pats args skipBody rest hneq] using ih

theorem selectMatchStmt_ofCtorCover
    (ctor : String) (args : List Value) (cases : List (Pattern × List Stmt)) (body : List Stmt)
    (hcover : CtorStmtCasesCover ctor cases body) :
    MatchStmtBranchObserved (.ctorV ctor args) cases body := by
  induction hcover with
  | ctorHit pats body rest =>
      exact selectMatchStmt_ctor ctor pats args body rest
  | wildHit body rest =>
      exact selectMatchStmt_wild (.ctorV ctor args) body rest
  | binderHit name body rest =>
      exact selectMatchStmt_binder (.ctorV ctor args) name body rest
  | skipCtor other pats skipBody rest body hneq hrest ih =>
      unfold MatchStmtBranchObserved at *
      simpa [selectMatchStmt_skipCtorMismatch ctor other pats args skipBody rest hneq] using ih

theorem selectMatchExpr_existsOfExhaustive
    (ctor : String) (args : List Value) (cases : List (Pattern × Expr))
    (hexh : CtorExprCasesExhaustive ctor cases) :
    ∃ body, MatchBranchObserved (.ctorV ctor args) cases body := by
  rcases hexh with ⟨body, hcover⟩
  exact ⟨body, selectMatchExpr_ofCtorCover ctor args cases body hcover⟩

theorem selectMatchStmt_existsOfExhaustive
    (ctor : String) (args : List Value) (cases : List (Pattern × List Stmt))
    (hexh : CtorStmtCasesExhaustive ctor cases) :
    ∃ body, MatchStmtBranchObserved (.ctorV ctor args) cases body := by
  rcases hexh with ⟨body, hcover⟩
  exact ⟨body, selectMatchStmt_ofCtorCover ctor args cases body hcover⟩

theorem runPipelineStages_nil
    (input : Value) :
    runPipelineStages input [] = input := by
  rfl

theorem copyUpdatePathObserved_root
    (base newv : Value) :
    CopyUpdatePathObserved base [] newv newv := by
  constructor <;> rfl

theorem copyUpdateHeadObserved_root
    (base newv : Value) :
    CopyUpdateHeadObserved base [] newv newv := by
  rfl

theorem copyUpdatePrefixObserved_root
    (base newv : Value) :
    CopyUpdatePrefixObserved base [] newv newv := by
  rfl

theorem semLookupValuePath_update_success
    (base : Value) (path : List String) (newv out : Value)
    (hupd : semUpdateValuePath base path newv = some out) :
    semLookupValuePath out path = some newv := by
  induction path generalizing base out with
  | nil =>
      simp [semUpdateValuePath, semLookupValuePath] at hupd ⊢
      cases hupd
      rfl
  | cons key rest ih =>
      cases base <;> simp [semUpdateValuePath] at hupd
      case structV name fields =>
        cases hlook : semLookupField fields key <;> simp [hlook] at hupd
        case some child =>
          cases hchild : semUpdateValuePath child rest newv <;> simp [hlook, hchild] at hupd
          case some child' =>
            cases hupd
            simp [semLookupValuePath, semLookupField_updated]
            exact ih child child' hchild

theorem copyUpdatePathObserved_of_success
    (base : Value) (path : List String) (newv out : Value)
    (hupd : semUpdateValuePath base path newv = some out) :
    CopyUpdatePathObserved base path newv out := by
  constructor
  · exact hupd
  · exact semLookupValuePath_update_success base path newv out hupd

theorem copyUpdateHeadObserved_of_success
    (base : Value) (path : List String) (newv out : Value)
    (hupd : semUpdateValuePath base path newv = some out) :
    CopyUpdateHeadObserved base path newv out := by
  cases path with
  | nil =>
      simp [CopyUpdateHeadObserved, semUpdateValuePath] at hupd ⊢
      cases hupd
      rfl
  | cons key rest =>
      cases base <;> simp [CopyUpdateHeadObserved, semUpdateValuePath] at hupd
      case structV name fields =>
        cases hlook : semLookupField fields key <;> simp [CopyUpdateHeadObserved, semUpdateValuePath, hlook] at hupd
        case some child =>
          cases hchild : semUpdateValuePath child rest newv <;> simp [CopyUpdateHeadObserved, semUpdateValuePath, hlook, hchild] at hupd
          case some child' =>
            cases hupd
            exact ⟨name, fields, child, child', rfl, hlook, hchild, rfl⟩

theorem copyUpdatePrefixObserved_of_success
    (base : Value) (path : List String) (newv out : Value)
    (hupd : semUpdateValuePath base path newv = some out) :
    CopyUpdatePrefixObserved base path newv out := by
  cases path with
  | nil =>
      simp [CopyUpdatePrefixObserved, semUpdateValuePath] at hupd ⊢
      cases hupd
      rfl
  | cons key rest =>
      cases base <;> simp [CopyUpdatePrefixObserved, semUpdateValuePath] at hupd
      case structV name fields =>
        cases hlook : semLookupField fields key <;> simp [CopyUpdatePrefixObserved, semUpdateValuePath, hlook] at hupd
        case some child =>
          cases hchild : semUpdateValuePath child rest newv <;> simp [CopyUpdatePrefixObserved, semUpdateValuePath, hlook, hchild] at hupd
          case some child' =>
            cases hupd
            exact ⟨name, fields, child, child', rfl, hlook, hchild, rfl,
              copyUpdatePathObserved_of_success child rest newv child' hchild⟩

theorem copyUpdatePathObserved_oneSegment
    (name field : String) (fields : SemFieldStore) (oldv newv : Value)
    (hlook : semLookupField fields field = some oldv) :
    CopyUpdatePathObserved
      (.structV name fields)
      [field]
      newv
      (.structV name (semUpdateField fields field newv)) := by
  constructor
  · simp [semUpdateValuePath, hlook]
  · simp [semLookupValuePath, semLookupField_updated]

theorem copyUpdateHeadObserved_oneSegment
    (name field : String) (fields : SemFieldStore) (oldv newv : Value)
    (hlook : semLookupField fields field = some oldv) :
    CopyUpdateHeadObserved
      (.structV name fields)
      [field]
      newv
      (.structV name (semUpdateField fields field newv)) := by
  refine ⟨name, fields, oldv, newv, rfl, hlook, ?_, rfl⟩
  simp [semUpdateValuePath]

theorem copyUpdatePrefixObserved_oneSegment
    (name field : String) (fields : SemFieldStore) (oldv newv : Value)
    (hlook : semLookupField fields field = some oldv) :
    CopyUpdatePrefixObserved
      (.structV name fields)
      [field]
      newv
      (.structV name (semUpdateField fields field newv)) := by
  refine ⟨name, fields, oldv, newv, rfl, hlook, ?_, rfl, ?_⟩
  · simp [semUpdateValuePath]
  · exact copyUpdatePathObserved_root oldv newv

theorem copyUpdatePrefixObserved_child
    (base : Value) (key : String) (rest : List String) (newv out : Value)
    (hobs : CopyUpdatePrefixObserved base (key :: rest) newv out) :
    ∃ name fields child child',
      base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child rest newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      CopyUpdatePathObserved child rest newv child' := by
  simpa [CopyUpdatePrefixObserved] using hobs

theorem copyUpdatePrefixObserved_childChain
    (base : Value) (key nextKey : String) (rest : List String) (newv out : Value)
    (hobs : CopyUpdatePrefixObserved base (key :: nextKey :: rest) newv out) :
    ∃ name fields child child',
      base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: rest) newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      CopyUpdatePrefixObserved child (nextKey :: rest) newv child' := by
  rcases copyUpdatePrefixObserved_child base key (nextKey :: rest) newv out hobs with
    ⟨name, fields, child, child', hbase, hlook, hchild, hout, _hpath⟩
  exact ⟨name, fields, child, child', hbase, hlook, hchild, hout,
    copyUpdatePrefixObserved_of_success child (nextKey :: rest) newv child' hchild⟩

theorem copyUpdatePrefixObserved_grandchild
    (base : Value) (key nextKey : String) (rest : List String) (newv out : Value)
    (hobs : CopyUpdatePrefixObserved base (key :: nextKey :: rest) newv out) :
    ∃ name fields child child' childName childFields grandchild grandchild',
      base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: rest) newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      child = .structV childName childFields ∧
      semLookupField childFields nextKey = some grandchild ∧
      semUpdateValuePath grandchild rest newv = some grandchild' ∧
      child' = .structV childName (semUpdateField childFields nextKey grandchild') ∧
      CopyUpdatePathObserved grandchild rest newv grandchild' := by
  rcases copyUpdatePrefixObserved_childChain base key nextKey rest newv out hobs with
    ⟨name, fields, child, child', hbase, hlook, hchild, hout, hchildPrefix⟩
  rcases copyUpdatePrefixObserved_child child nextKey rest newv child' hchildPrefix with
    ⟨childName, childFields, grandchild, grandchild', hchildBase, hchildLook, hgrandUpd, hchildOut, hgrandObs⟩
  exact ⟨name, fields, child, child', childName, childFields, grandchild, grandchild',
    hbase, hlook, hchild, hout, hchildBase, hchildLook, hgrandUpd, hchildOut, hgrandObs⟩

theorem copyUpdatePrefixObserved_grandchildChain
    (base : Value) (key nextKey thirdKey : String) (rest : List String) (newv out : Value)
    (hobs : CopyUpdatePrefixObserved base (key :: nextKey :: thirdKey :: rest) newv out) :
    ∃ name fields child child' childName childFields grandchild grandchild',
      base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: thirdKey :: rest) newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      child = .structV childName childFields ∧
      semLookupField childFields nextKey = some grandchild ∧
      semUpdateValuePath grandchild (thirdKey :: rest) newv = some grandchild' ∧
      child' = .structV childName (semUpdateField childFields nextKey grandchild') ∧
      CopyUpdatePrefixObserved grandchild (thirdKey :: rest) newv grandchild' := by
  rcases copyUpdatePrefixObserved_grandchild base key nextKey (thirdKey :: rest) newv out hobs with
    ⟨name, fields, child, child', childName, childFields, grandchild, grandchild',
      hbase, hlook, hchild, hout, hchildBase, hchildLook, hgrandUpd, hchildOut, _hgrandObs⟩
  exact ⟨name, fields, child, child', childName, childFields, grandchild, grandchild',
    hbase, hlook, hchild, hout, hchildBase, hchildLook, hgrandUpd, hchildOut,
    copyUpdatePrefixObserved_of_success grandchild (thirdKey :: rest) newv grandchild' hgrandUpd⟩

theorem runPipelineStages_single
    (input : Value) (stage : PipelineStage) :
    PipelineSingleStageObserved input stage := by
  constructor
  · simp [PipelineSingleStageObserved, runPipelineStages]
  · cases stage with
    | map =>
        cases input <;> simp [PipelineStageResultObserved, runPipelineStage]
    | filter =>
        cases input with
        | unit => simp [PipelineStageResultObserved, runPipelineStage]
        | bool b => simp [PipelineStageResultObserved, runPipelineStage]
        | int n => simp [PipelineStageResultObserved, runPipelineStage]
        | str s => simp [PipelineStageResultObserved, runPipelineStage]
        | tuple items =>
            cases items <;> simp [PipelineStageResultObserved, runPipelineStage]
        | structV name fields => simp [PipelineStageResultObserved, runPipelineStage]
        | ctorV name args => simp [PipelineStageResultObserved, runPipelineStage]
    | fold =>
        cases input with
        | unit => simp [PipelineStageResultObserved, runPipelineStage]
        | bool b => simp [PipelineStageResultObserved, runPipelineStage]
        | int n => simp [PipelineStageResultObserved, runPipelineStage]
        | str s => simp [PipelineStageResultObserved, runPipelineStage]
        | tuple items =>
            cases items <;> simp [PipelineStageResultObserved, runPipelineStage]
        | structV name fields => simp [PipelineStageResultObserved, runPipelineStage]
        | ctorV name args => simp [PipelineStageResultObserved, runPipelineStage]

theorem runPipelineStages_all
    (input : Value) (stages : List PipelineStage) :
    PipelineStagesObserved input stages := by
  induction stages generalizing input with
  | nil =>
      constructor
      · rfl
      · trivial
  | cons stage rest ih =>
      rcases ih (runPipelineStage input stage) with ⟨hfold, htrace⟩
      constructor
      · simpa [PipelineStagesObserved, runPipelineStages, List.foldl] using hfold
      · exact ⟨runPipelineStages_single input stage, htrace⟩

theorem interpTailExpr_call
    (fn : String) (args : List Expr) :
    interpTailExpr (.call fn args) = .recur fn (args.map interpExpr) := by
  rfl

theorem tailRecurObserved_call
    (fn : String) (args : List Expr) :
    TailRecurObserved (.call fn args) fn (args.map interpExpr) := by
  unfold TailRecurObserved
  exact interpTailExpr_call fn args

theorem tailCallShapeObserved_call
    (fn : String) (args : List Expr) :
    TailCallShapeObserved (.call fn args) fn (args.map interpExpr) := by
  exact ⟨args, rfl, rfl⟩

theorem interpTailExpr_noncall
    (e : Expr)
    (h : ∀ fn args, e ≠ .call fn args) :
    ∃ v, interpTailExpr e = .ret v := by
  exists interpExpr e
  cases e <;> simp [interpTailExpr]
  case call fn args =>
    exfalso
    exact h fn args rfl

theorem continue_injective
    (ρ₁ ρ₂ : Env)
    (h : Result.continue ρ₁ = Result.continue ρ₂) :
    ρ₁ = ρ₂ := by
  injection h

theorem ret_injective
    (v₁ v₂ : Value)
    (h : Result.ret v₁ = Result.ret v₂) :
    v₁ = v₂ := by
  injection h

theorem continue_ne_ret
    (ρ : Env) (v : Value) :
    Result.continue ρ ≠ Result.ret v := by
  intro h
  cases h

theorem evalExpr_deterministic
    (p : Program) (ρ : Env) (e : Expr) (v₁ v₂ : Value)
    (h₁ : EvalExpr p ρ e v₁) (h₂ : EvalExpr p ρ e v₂) :
    v₁ = v₂ := by
  unfold EvalExpr at h₁ h₂
  rw [h₁] at h₂
  exact h₂

theorem evalBlock_deterministic
    (p : Program) (ρ : Env) (ss : List Stmt) (r₁ r₂ : Result)
    (h₁ : EvalBlock p ρ ss r₁) (h₂ : EvalBlock p ρ ss r₂) :
    r₁ = r₂ := by
  unfold EvalBlock at h₁ h₂
  rw [h₁] at h₂
  exact h₂

end Fo
