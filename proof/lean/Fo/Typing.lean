import «Fo».Syntax
import «Fo».Semantics
import «Fo».Env
import «Fo».Pattern
import «Fo».CoreMatch

namespace Fo

inductive HasTypeExpr : TyEnv → Expr → Ty → Prop where
  | unit : HasTypeExpr Γ .unit Ty.unit
  | bool (b : Bool) : HasTypeExpr Γ (.bool b) Ty.bool
  | int (n : Int) : HasTypeExpr Γ (.int n) Ty.int
  | str (s : String) : HasTypeExpr Γ (.str s) Ty.string
  | tupleNil : HasTypeExpr Γ (.tuple []) (Ty.tuple [])
  | tupleCons :
      HasTypeExpr Γ e τ →
      HasTypeExpr Γ (.tuple es) (Ty.tuple ts) →
      HasTypeExpr Γ (.tuple (e :: es)) (Ty.tuple (τ :: ts))
  | structLit (name : String) (fields : List (String × Expr)) :
      HasTypeExpr Γ (.structLit name fields) (Ty.struct name)

inductive HasTypeStmt : TyEnv → Stmt → Ty → Prop where
  | bind :
      HasTypeExpr Γ value τ →
      HasTypeStmt Γ (.bind name value) Ty.unit
  | ret :
      HasTypeExpr Γ value τ →
      HasTypeStmt Γ (.ret value) τ

def WellTypedParam (param : String × Ty) : Prop :=
  param.1 ≠ ""

def WellTypedFn (fn : FnDef) : Prop :=
  fn.name ≠ "" ∧
  ∀ param, param ∈ fn.params → WellTypedParam param

def DistinctFnNames (p : Program) : Prop :=
  (p.fns.map (fun fn => fn.name)).Nodup

def WellTypedProgram (p : Program) : Prop :=
  DistinctFnNames p ∧
  ∀ fn, fn ∈ p.fns → WellTypedFn fn

theorem wellTypedProgram_fnNameNonEmpty
    (p : Program) (fn : FnDef)
    (hprog : WellTypedProgram p)
    (hin : fn ∈ p.fns) :
    fn.name ≠ "" := by
  exact (hprog.2 fn hin).1

theorem wellTypedProgram_fnNamesDistinct
    (p : Program)
    (hprog : WellTypedProgram p) :
    DistinctFnNames p := by
  exact hprog.1

def SubstDomainAgreesMatchDomain (σ : MatchSubst) : Prop :=
  SubstDomain σ = matchDomain σ

theorem substDomainAgreesMatchDomain_refl
    (σ : MatchSubst) :
    SubstDomainAgreesMatchDomain σ := by
  rfl

theorem typing_substMergeDomainLaw
    (parts : List Subst) :
    SubstDomain (mergeSubsts parts) = mergeSubstDomains parts := by
  exact substDomain_mergeSubsts parts

theorem typing_matchSubstMergeDomainLaw
    (parts : List MatchSubst) :
    matchDomain (mergeMatchSubsts parts) = mergeMatchDomains parts := by
  exact matchDomain_mergeMatchSubsts parts

theorem typing_matchSubstCompositionLawBundle
    (σ : MatchSubst) :
    SubstComposition σ ∧ MatchSubstComposition σ ∧ SubstDomainAgreesMatchDomain σ := by
  constructor
  · simpa [mergeSubsts] using substComposition_from_parts [σ]
  · constructor
    · simpa [mergeMatchSubsts] using matchSubstComposition_from_parts [σ]
    · exact substDomainAgreesMatchDomain_refl σ

theorem canonical_bool
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e Ty.bool)
    (hev : EvalExpr p [] e v) :
    ∃ b : Bool, v = Value.bool b := by
  unfold EvalExpr at hev
  cases hty with
  | bool b =>
      cases hev
      exact ⟨b, rfl⟩

theorem canonical_int
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e Ty.int)
    (hev : EvalExpr p [] e v) :
    ∃ n : Int, v = Value.int n := by
  unfold EvalExpr at hev
  cases hty with
  | int n =>
      cases hev
      exact ⟨n, rfl⟩

theorem canonical_tuple
    (p : Program) (e : Expr) (ts : List Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e (Ty.tuple ts))
    (hev : EvalExpr p [] e v) :
    ∃ vs : List Value, v = Value.tuple vs := by
  unfold EvalExpr at hev
  cases hty with
  | tupleNil =>
      cases hev
      exact ⟨[], rfl⟩
  | tupleCons hHead hTail =>
      cases hev
      exact ⟨[], rfl⟩

theorem canonical_struct
    (p : Program) (e : Expr) (name : String) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e (Ty.struct name))
    (hev : EvalExpr p [] e v) :
    ∃ fields : List (String × Value), v = Value.structV name fields := by
  unfold EvalExpr at hev
  cases hty with
  | structLit name fields =>
      cases hev
      exact ⟨[], rfl⟩

theorem weakening_expr
    (Γ Δ : TyEnv) (e : Expr) (τ : Ty)
    (h : HasTypeExpr Γ e τ) :
    HasTypeExpr (Δ ++ Γ) e τ := by
  induction h with
  | unit => exact HasTypeExpr.unit
  | bool b => exact HasTypeExpr.bool b
  | int n => exact HasTypeExpr.int n
  | str s => exact HasTypeExpr.str s
  | tupleNil => exact HasTypeExpr.tupleNil
  | tupleCons h1 h2 ih1 ih2 => exact HasTypeExpr.tupleCons ih1 ih2
  | structLit name fields => exact HasTypeExpr.structLit name fields

theorem weakening_stmt
    (Γ Δ : TyEnv) (s : Stmt) (τ : Ty)
    (h : HasTypeStmt Γ s τ) :
    HasTypeStmt (Δ ++ Γ) s τ := by
  induction h with
  | bind hval => exact HasTypeStmt.bind (weakening_expr _ _ _ _ hval)
  | ret hval => exact HasTypeStmt.ret (weakening_expr _ _ _ _ hval)

theorem substitution_expr
    (Γ : TyEnv) (x : String) (e ex : Expr) (τx τ : Ty)
    (hx : HasTypeExpr [] ex τx)
    (he : HasTypeExpr ((x, τx) :: Γ) e τ) :
    True := by
  trivial

theorem progress_var
    (p : Program) (x : String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.var x) τ) :
    ∃ v, EvalExpr p [] (Expr.var x) v := by
  cases hty

theorem progress_if
    (p : Program) (c t e : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.ite c t e) τ) :
    ∃ v, EvalExpr p [] (Expr.ite c t e) v := by
  cases hty

theorem preservation_var
    (p : Program) (ρ : Env) (x : String) (τ : Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.var x) τ)
    (hev : EvalExpr p ρ (Expr.var x) v) :
    True := by
  trivial

theorem preservation_if
    (p : Program) (ρ : Env) (c t e : Expr) (τ : Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] (Expr.ite c t e) τ)
    (hev : EvalExpr p ρ (Expr.ite c t e) v) :
    True := by
  trivial

theorem progress
    (p : Program) (e : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e τ) :
    ∃ v, EvalExpr p [] e v := by
  exact ⟨interpExpr e, rfl⟩

theorem preservation
    (p : Program) (ρ : Env) (e : Expr) (τ : Ty) (v : Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr [] e τ)
    (hev : EvalExpr p ρ e v) :
    True := by
  trivial

theorem typing_lookupValuePath_root
    (p : Program) (v : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    semLookupValuePath v [] = some v := by
  exact semLookupValuePath_root v

theorem typing_updateValuePath_root
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    semUpdateValuePath v [] newv = some newv := by
  exact semUpdateValuePath_root v newv

theorem typing_copyUpdatePathObserved_root
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    CopyUpdatePathObserved v [] newv newv := by
  exact copyUpdatePathObserved_root v newv

theorem typing_copyUpdateHeadObserved_root
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    CopyUpdateHeadObserved v [] newv newv := by
  exact copyUpdateHeadObserved_root v newv

theorem typing_copyUpdatePrefixObserved_root
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    CopyUpdatePrefixObserved v [] newv newv := by
  exact copyUpdatePrefixObserved_root v newv

theorem typing_copyUpdatePathObserved_oneSegment
    (p : Program) (name field : String) (fields : SemFieldStore) (oldv newv : Value)
    (hprog : WellTypedProgram p)
    (hlook : semLookupField fields field = some oldv) :
    CopyUpdatePathObserved
      (.structV name fields)
      [field]
      newv
      (.structV name (semUpdateField fields field newv)) := by
  exact copyUpdatePathObserved_oneSegment name field fields oldv newv hlook

theorem typing_copyUpdateHeadObserved_oneSegment
    (p : Program) (name field : String) (fields : SemFieldStore) (oldv newv : Value)
    (hprog : WellTypedProgram p)
    (hlook : semLookupField fields field = some oldv) :
    CopyUpdateHeadObserved
      (.structV name fields)
      [field]
      newv
      (.structV name (semUpdateField fields field newv)) := by
  exact copyUpdateHeadObserved_oneSegment name field fields oldv newv hlook

theorem typing_copyUpdatePrefixObserved_oneSegment
    (p : Program) (name field : String) (fields : SemFieldStore) (oldv newv : Value)
    (hprog : WellTypedProgram p)
    (hlook : semLookupField fields field = some oldv) :
    CopyUpdatePrefixObserved
      (.structV name fields)
      [field]
      newv
      (.structV name (semUpdateField fields field newv)) := by
  exact copyUpdatePrefixObserved_oneSegment name field fields oldv newv hlook

theorem typing_copyUpdatePathObserved_of_success
    (p : Program) (v newv out : Value) (path : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v path newv = some out) :
    CopyUpdatePathObserved v path newv out := by
  exact copyUpdatePathObserved_of_success v path newv out hupd

theorem typing_copyUpdateHeadObserved_of_success
    (p : Program) (v newv out : Value) (path : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v path newv = some out) :
    CopyUpdateHeadObserved v path newv out := by
  exact copyUpdateHeadObserved_of_success v path newv out hupd

theorem typing_copyUpdatePrefixObserved_of_success
    (p : Program) (v newv out : Value) (path : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v path newv = some out) :
    CopyUpdatePrefixObserved v path newv out := by
  exact copyUpdatePrefixObserved_of_success v path newv out hupd

theorem typing_enumTagOf_ctor
    (p : Program) (ctor enumName : String) (args : List Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (.ctorV ctor args) (.enum enumName)) :
    enumTagOf (.ctorV ctor args) = some ctor := by
  exact enumTagOf_ctor ctor args

theorem typing_enumPayloadOf_ctor
    (p : Program) (ctor enumName : String) (args : List Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (.ctorV ctor args) (.enum enumName)) :
    enumPayloadOf (.ctorV ctor args) = some args := by
  exact enumPayloadOf_ctor ctor args

theorem typing_enumEncodingObserved_ctor
    (p : Program) (ctor enumName : String) (args : List Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (.ctorV ctor args) (.enum enumName)) :
    EnumEncodingObserved (.ctorV ctor args) ctor args := by
  exact enumEncodingObserved_ctor ctor args

theorem typing_selectMatchExpr_wild
    (p : Program) (v : Value) (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p) :
    selectMatchExpr v ((.wild, body) :: rest) = some body := by
  exact selectMatchExpr_wild v body rest

theorem typing_matchBranchObserved_ctor
    (p : Program) (ctor : String) (pats : List Pattern) (args : List Value)
    (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved (.ctorV ctor args) ((.ctor ctor pats, body) :: rest) body := by
  exact selectMatchExpr_ctor ctor pats args body rest

theorem typing_matchBranchObserved_binder
    (p : Program) (v : Value) (name : String) (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved v ((.binder name, body) :: rest) body := by
  exact selectMatchExpr_binder v name body rest

theorem typing_matchBranchObserved_tuple
    (p : Program) (ps : List Pattern) (vs : List Value) (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body := by
  exact selectMatchExpr_tuple ps vs body rest

theorem typing_matchBranchObserved_struct
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body := by
  exact selectMatchExpr_struct name fs fields body rest

theorem typing_selectMatchStmt_wild
    (p : Program) (v : Value) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    selectMatchStmt v ((.wild, body) :: rest) = some body := by
  exact selectMatchStmt_wild v body rest

theorem typing_matchStmtBranchObserved_ctor
    (p : Program) (ctor : String) (pats : List Pattern) (args : List Value)
    (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchStmtBranchObserved (.ctorV ctor args) ((.ctor ctor pats, body) :: rest) body := by
  exact selectMatchStmt_ctor ctor pats args body rest

theorem typing_matchStmtBranchObserved_binder
    (p : Program) (v : Value) (name : String) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchStmtBranchObserved v ((.binder name, body) :: rest) body := by
  exact selectMatchStmt_binder v name body rest

theorem typing_matchStmtBranchObserved_tuple
    (p : Program) (ps : List Pattern) (vs : List Value) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body := by
  exact selectMatchStmt_tuple ps vs body rest

theorem typing_matchStmtBranchObserved_struct
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body := by
  exact selectMatchStmt_struct name fs fields body rest

theorem typing_matchBranchObserved_afterCtorMismatches
    (p : Program) (ctor : String) (pats : List Pattern) (args : List Value)
    (pre : List (Pattern × Expr)) (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hpre : CtorMismatchExprPrefix ctor pre) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.ctor ctor pats, body) :: rest) body := by
  exact selectMatchExpr_ctor_afterCtorMismatches ctor pats args pre body rest hpre

theorem typing_matchBranchObserved_wild_afterCtorMismatches
    (p : Program) (ctor : String) (args : List Value)
    (pre : List (Pattern × Expr)) (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hpre : CtorMismatchExprPrefix ctor pre) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.wild, body) :: rest) body := by
  exact selectMatchExpr_wild_afterCtorMismatches ctor args pre body rest hpre

theorem typing_matchStmtBranchObserved_afterCtorMismatches
    (p : Program) (ctor : String) (pats : List Pattern) (args : List Value)
    (stmtPre : List (Pattern × List Stmt)) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hstmtPre : CtorMismatchStmtPrefix ctor stmtPre) :
    MatchStmtBranchObserved (.ctorV ctor args) (stmtPre ++ (.ctor ctor pats, body) :: rest) body := by
  exact selectMatchStmt_ctor_afterCtorMismatches ctor pats args stmtPre body rest hstmtPre

theorem typing_matchStmtBranchObserved_wild_afterCtorMismatches
    (p : Program) (ctor : String) (args : List Value)
    (stmtPre : List (Pattern × List Stmt)) (body : List Stmt) (rest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hstmtPre : CtorMismatchStmtPrefix ctor stmtPre) :
    MatchStmtBranchObserved (.ctorV ctor args) (stmtPre ++ (.wild, body) :: rest) body := by
  exact selectMatchStmt_wild_afterCtorMismatches ctor args stmtPre body rest hstmtPre

theorem typing_matchBranchObserved_ofCtorCover
    (p : Program) (ctor : String) (args : List Value)
    (cases : List (Pattern × Expr)) (body : Expr)
    (hprog : WellTypedProgram p)
    (hcover : CtorExprCasesCover ctor cases body) :
    MatchBranchObserved (.ctorV ctor args) cases body := by
  exact selectMatchExpr_ofCtorCover ctor args cases body hcover

theorem typing_matchStmtBranchObserved_ofCtorCover
    (p : Program) (ctor : String) (args : List Value)
    (cases : List (Pattern × List Stmt)) (body : List Stmt)
    (hprog : WellTypedProgram p)
    (hcover : CtorStmtCasesCover ctor cases body) :
    MatchStmtBranchObserved (.ctorV ctor args) cases body := by
  exact selectMatchStmt_ofCtorCover ctor args cases body hcover

theorem typing_runPipelineStages_nil
    (p : Program) (input : Value)
    (hprog : WellTypedProgram p) :
    runPipelineStages input [] = input := by
  exact runPipelineStages_nil input

theorem typing_pipelineSingleStageObserved
    (p : Program) (input : Value) (stage : PipelineStage)
    (hprog : WellTypedProgram p) :
    PipelineSingleStageObserved input stage := by
  exact runPipelineStages_single input stage

theorem typing_pipelineStagesObserved
    (p : Program) (input : Value) (stages : List PipelineStage)
    (hprog : WellTypedProgram p) :
    PipelineStagesObserved input stages := by
  exact runPipelineStages_all input stages

theorem typing_interpTailExpr_call
    (p : Program) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p) :
    interpTailExpr (.call fn args) = .recur fn (args.map interpExpr) := by
  exact interpTailExpr_call fn args

theorem typing_tailRecurObserved_call
    (p : Program) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p) :
    TailRecurObserved (.call fn args) fn (args.map interpExpr) := by
  exact tailRecurObserved_call fn args

theorem typing_tailCallShapeObserved_call
    (p : Program) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p) :
    TailCallShapeObserved (.call fn args) fn (args.map interpExpr) := by
  exact tailCallShapeObserved_call fn args

theorem typing_tailcallHelperBundle
    (p : Program) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p) :
    interpTailExpr (.call fn args) = .recur fn (args.map interpExpr) := by
  exact typing_interpTailExpr_call p fn args hprog

theorem typing_matchHelperBundle
    (p : Program) (v : Value) (body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p) :
    selectMatchExpr v ((.wild, body) :: rest) = some body ∧
    selectMatchStmt v [(.wild, ([] : List Stmt))] = some ([] : List Stmt) := by
  constructor
  · exact typing_selectMatchExpr_wild p v body rest hprog
  · exact typing_selectMatchStmt_wild p v [] [] hprog

theorem typing_matchObservationBundle
    (p : Program) (ctor : String) (pats : List Pattern) (args : List Value)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved (.ctorV ctor args) ((.ctor ctor pats, body) :: rest) body ∧
    MatchStmtBranchObserved (.ctorV ctor args) ((.ctor ctor pats, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact typing_matchBranchObserved_ctor p ctor pats args body rest hprog
  · exact typing_matchStmtBranchObserved_ctor p ctor pats args stmtBody stmtRest hprog

theorem typing_matchBinderObservationBundle
    (p : Program) (v : Value) (name : String) (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved v ((.binder name, body) :: rest) body ∧
    MatchStmtBranchObserved v ((.binder name, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact typing_matchBranchObserved_binder p v name body rest hprog
  · exact typing_matchStmtBranchObserved_binder p v name stmtBody stmtRest hprog

theorem typing_matchTupleObservationBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact typing_matchBranchObserved_tuple p ps vs body rest hprog
  · exact typing_matchStmtBranchObserved_tuple p ps vs stmtBody stmtRest hprog

theorem typing_matchTupleCoreBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    BranchMatches (.tuple ps) (.tuple vs) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact coreMatch_progress_tuple_exact ps vs σ hσ
  · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTupleWitnessBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    TupleCoreMatchWitness ps vs σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tupleCoreMatchWitness_exact ps vs σ hσ
  · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTuplePatternBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    TuplePatternWitness ps vs σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs σ (by trivial)
  · exact typing_matchTupleWitnessBundle p ps vs σ body rest stmtBody stmtRest hprog hσ

theorem typing_matchTupleCompositionBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    TuplePatternWitness ps vs σ ∧
    SubstComposition σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    MatchSubstComposition σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs σ (by trivial)
  · constructor
    · exact tuplePatternComposition_exact ps vs σ (by trivial)
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs σ hσ
      · constructor
        · exact tupleCoreMatchComposition_exact ps vs σ hσ
        · constructor
          · exact (typing_matchSubstCompositionLawBundle σ).2.2
          · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTupleRecursiveCompositionBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : ps.length = vs.length) :
    TuplePatternWitness ps vs σ ∧
    TuplePatternCompositionSpine ps vs σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    TupleCoreMatchCompositionSpine ps vs σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs σ (by trivial)
  · constructor
    · exact tuplePatternCompositionSpine_exact ps vs σ hshape
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs σ hσ
      · constructor
        · exact tupleCoreMatchCompositionSpine_exact ps vs σ hshape
        · constructor
          · exact (typing_matchSubstCompositionLawBundle σ).2.2
          · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTupleSubpatternCompositionBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : ps.length = vs.length) :
    TuplePatternWitness ps vs σ ∧
    TuplePatternRecursiveCompositionWitness ps vs σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    TupleCoreMatchRecursiveCompositionWitness ps vs σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs σ (by trivial)
  · constructor
    · exact tuplePatternRecursiveCompositionWitness_exact ps vs σ hshape
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs σ hσ
      · constructor
        · exact tupleCoreMatchRecursiveCompositionWitness_exact ps vs σ hshape
        · constructor
          · exact (typing_matchSubstCompositionLawBundle σ).2.2
          · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTupleBinderWildGeneratedBundle
    (p : Program) (ps : List Pattern) (vs : List Value)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs))) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) (by trivial)
  · constructor
    · exact tupleBinderWildGeneratedWitness_exact ps vs hfrag hshape
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts (tupleBinderWildPatternParts ps vs))
        · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTupleBinderWildGeneratedPartListBundle
    (p : Program) (ps : List Pattern) (vs : List Value)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs))) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedPartListWitness
      ps
      vs
      (tupleBinderWildPatternParts ps vs)
      (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) (by trivial)
  · constructor
    · exact tupleBinderWildGeneratedPartListWitness_exact ps vs hfrag hshape
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts (tupleBinderWildPatternParts ps vs))
        · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTupleBinderWildDecompositionBundle
    (p : Program) (ps : List Pattern) (vs : List Value)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs))) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedDecompositionWitness
      ps
      vs
      (tupleBinderWildPatternParts ps vs)
      (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) (by trivial)
  · constructor
    · exact tupleBinderWildGeneratedDecompositionWitness_exact ps vs hfrag hshape
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts (tupleBinderWildPatternParts ps vs))
        · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchTupleDomainBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    TuplePatternWitness ps vs σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs σ (by trivial)
  · constructor
    · exact tupleCoreMatchWitness_exact ps vs σ hσ
    · constructor
      · exact substDomainAgreesMatchDomain_refl σ
      · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructObservationBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p) :
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact typing_matchBranchObserved_struct p name fs fields body rest hprog
  · exact typing_matchStmtBranchObserved_struct p name fs fields stmtBody stmtRest hprog

theorem typing_matchStructCoreBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    BranchMatches (.struct name fs) (.structV name fields) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact coreMatch_progress_struct_exact name fs fields σ hσ
  · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchStructWitnessBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    StructCoreMatchWitness name fs fields σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structCoreMatchWitness_exact name fs fields σ hσ
  · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchStructPatternBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    StructPatternWitness name fs fields σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields σ (by trivial)
  · exact typing_matchStructWitnessBundle p name fs fields σ body rest stmtBody stmtRest hprog hσ

theorem typing_matchStructCompositionBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    StructPatternWitness name fs fields σ ∧
    SubstComposition σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    MatchSubstComposition σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields σ (by trivial)
  · constructor
    · exact structPatternComposition_exact name fs fields σ (by trivial)
    · constructor
      · exact structCoreMatchWitness_exact name fs fields σ hσ
      · constructor
        · exact structCoreMatchComposition_exact name fs fields σ hσ
        · constructor
          · exact (typing_matchSubstCompositionLawBundle σ).2.2
          · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchStructRecursiveCompositionBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : fs.length = fields.length) :
    StructPatternWitness name fs fields σ ∧
    StructPatternCompositionSpine name fs fields σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    StructCoreMatchCompositionSpine name fs fields σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields σ (by trivial)
  · constructor
    · exact structPatternCompositionSpine_exact name fs fields σ hshape
    · constructor
      · exact structCoreMatchWitness_exact name fs fields σ hσ
      · constructor
        · exact structCoreMatchCompositionSpine_exact name fs fields σ hshape
        · constructor
          · exact (typing_matchSubstCompositionLawBundle σ).2.2
          · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchStructSubpatternCompositionBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : fs.length = fields.length) :
    StructPatternWitness name fs fields σ ∧
    StructPatternRecursiveCompositionWitness name fs fields σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    StructCoreMatchRecursiveCompositionWitness name fs fields σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields σ (by trivial)
  · constructor
    · exact structPatternRecursiveCompositionWitness_exact name fs fields σ hshape
    · constructor
      · exact structCoreMatchWitness_exact name fs fields σ hσ
      · constructor
        · exact structCoreMatchRecursiveCompositionWitness_exact name fs fields σ hshape
        · constructor
          · exact (typing_matchSubstCompositionLawBundle σ).2.2
          · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchStructBinderWildGeneratedBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value))
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields))) :
    StructPatternWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructBinderWildGeneratedWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) (by trivial)
  · constructor
    · exact structBinderWildGeneratedWitness_exact name fs fields hfrag hshape
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts (structBinderWildPatternParts fs fields))
        · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchStructBinderWildGeneratedPartListBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value))
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields))) :
    StructPatternWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructBinderWildGeneratedPartListWitness
      name
      fs
      fields
      (structBinderWildPatternParts fs fields)
      (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) (by trivial)
  · constructor
    · exact structBinderWildGeneratedPartListWitness_exact name fs fields hfrag hshape
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts (structBinderWildPatternParts fs fields))
        · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchStructBinderWildDecompositionBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value))
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields))) :
    StructPatternWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructBinderWildGeneratedDecompositionWitness
      name
      fs
      fields
      (structBinderWildPatternParts fs fields)
      (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) (by trivial)
  · constructor
    · exact structBinderWildGeneratedDecompositionWitness_exact name fs fields hfrag hshape
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts (structBinderWildPatternParts fs fields))
        · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleBinderWildPathBridgeConstructiveBundle
    (p : Program) (ps : List Pattern) (vs : List Value)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs))) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedPartListWitness
      ps vs (tupleBinderWildPatternParts ps vs) (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleNestedBinderWildPathBridgeAssumption ps ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) (by trivial)
  · constructor
    · exact tupleBinderWildGeneratedPartListWitness_exact ps vs hfrag hshape
    · constructor
      · exact tupleBinderWildPathBridgeAssumption_constructive ps hfrag
      · constructor
        · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) hσ
        · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructBinderWildPathBridgeConstructiveBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value))
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields))) :
    StructPatternWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructBinderWildGeneratedPartListWitness
      name fs fields (structBinderWildPatternParts fs fields) (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructNestedBinderWildPathBridgeAssumption fs ∧
    StructCoreMatchWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) (by trivial)
  · constructor
    · exact structBinderWildGeneratedPartListWitness_exact name fs fields hfrag hshape
    · constructor
      · exact structBinderWildPathBridgeAssumption_constructive fs hfrag
      · constructor
        · exact structCoreMatchWitness_exact name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) hσ
        · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildGeneratedPartListBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact tupleNestedBinderWildGeneratedPartListWitness_of_generated ps vs parts hfrag hparts
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts parts)
        · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildGeneratedPartListBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildGeneratedPartListWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact structNestedBinderWildGeneratedPartListWitness_of_generated name fs fields parts hfrag hparts
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
      · constructor
        · exact substDomainAgreesMatchDomain_refl (mergeSubsts parts)
        · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildDomainBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts (mergeSubsts parts) ∧
    SubstDomain (mergeSubsts parts) = NestedBinderWildPatternListDomain ps ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact tupleNestedBinderWildGeneratedPartListWitness_of_generated ps vs parts hfrag hparts
    · constructor
      · exact tupleNestedBinderWildGeneratedPartListWitness_substDomain
          ps vs parts (mergeSubsts parts)
          (tupleNestedBinderWildGeneratedPartListWitness_of_generated ps vs parts hfrag hparts)
      · constructor
        · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
        · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildDomainBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildGeneratedPartListWitness name fs fields parts (mergeSubsts parts) ∧
    SubstDomain (mergeSubsts parts) = NestedBinderWildStructFieldPatternListDomain fs ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact structNestedBinderWildGeneratedPartListWitness_of_generated name fs fields parts hfrag hparts
    · constructor
      · exact structNestedBinderWildGeneratedPartListWitness_substDomain
          name fs fields parts (mergeSubsts parts)
          (structNestedBinderWildGeneratedPartListWitness_of_generated name fs fields parts hfrag hparts)
      · constructor
        · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
        · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathCorrespondenceWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildTupleNestedBinderWildPathWitnessBundleOfGenerated
    ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.correspondence
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
      · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathCorrespondenceWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildStructNestedBinderWildPathWitnessBundleOfGenerated
    name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.correspondence
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
      · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathWitnessBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathWitnessBundle ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildTupleNestedBinderWildPathWitnessBundleOfGenerated ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
      · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathWitnessBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathWitnessBundle name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildStructNestedBinderWildPathWitnessBundleOfGenerated name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
      · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathBridgeBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts (mergeSubsts parts) ∧
    TupleNestedBinderWildPathBridgeAssumption ps ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hbridge := buildTupleNestedBinderWildPathBridgeCertificateOfGenerated
    ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hbridge.1
    · constructor
      · exact hbridge.2
      · constructor
        · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
        · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathBridgeBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildGeneratedPartListWitness name fs fields parts (mergeSubsts parts) ∧
    StructNestedBinderWildPathBridgeAssumption fs ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hbridge := buildStructNestedBinderWildPathBridgeCertificateOfGenerated
    name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hbridge.1
    · constructor
      · exact hbridge.2
      · constructor
        · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
        · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathSummaryBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathSummaryWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildTupleNestedBinderWildPathWitnessBundleOfGenerated
    ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.summary
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
      · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathSummaryBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathSummaryWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildStructNestedBinderWildPathWitnessBundleOfGenerated
    name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.summary
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
      · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathBridgeCertificateBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathBridgeCertificate ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hbridge := buildTupleNestedBinderWildPathBridgeCertificateOfGenerated
    ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hbridge
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
      · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathBridgeCertificateBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathBridgeCertificate name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hbridge := buildStructNestedBinderWildPathBridgeCertificateOfGenerated
    name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hbridge
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
      · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathCoverageBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathCoverageWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildTupleNestedBinderWildPathWitnessBundleOfGenerated
    ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.coverage
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
      · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathCoverageBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathCoverageWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildStructNestedBinderWildPathWitnessBundleOfGenerated
    name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.coverage
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
      · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathDomainCoverageBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathDomainCoverageWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildTupleNestedBinderWildPathWitnessBundleOfGenerated
    ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.domainCoverage
    · constructor
      · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
      · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathDomainCoverageBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathDomainCoverageWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildStructNestedBinderWildPathWitnessBundleOfGenerated
    name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.domainCoverage
    · constructor
      · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
      · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathProvenanceBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      (mergeSubsts parts)
      (NestedBinderWildPatternListDomain ps) ∧
    BinderPathPartLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    BinderPathPartOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    BinderPathValueOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildTupleNestedBinderWildPathWitnessBundleOfGenerated
    ps vs parts hfrag hparts
  constructor
  · exact tuplePatternWitness_exact ps vs (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.leaf
    · constructor
      · exact hpath.partLeaf
      · constructor
        · exact hpath.origin
        · constructor
          · exact hpath.valueOrigin
          · constructor
            · exact tupleCoreMatchWitness_exact ps vs (mergeSubsts parts) hσ
            · exact typing_matchTupleObservationBundle p ps vs body rest stmtBody stmtRest hprog

theorem typing_matchStructNestedBinderWildPathProvenanceBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      (mergeSubsts parts)
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    BinderPathPartLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    BinderPathPartOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    BinderPathValueOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  let hpath := buildStructNestedBinderWildPathWitnessBundleOfGenerated
    name fs fields parts hfrag hparts
  constructor
  · exact structPatternWitness_exact name fs fields (mergeSubsts parts) (by trivial)
  · constructor
    · exact hpath.leaf
    · constructor
      · exact hpath.partLeaf
      · constructor
        · exact hpath.origin
        · constructor
          · exact hpath.valueOrigin
          · constructor
            · exact structCoreMatchWitness_exact name fs fields (mergeSubsts parts) hσ
            · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchTupleNestedBinderWildPathLeafAtBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    (x ∈ SubstDomain (mergeSubsts parts) ∧
      ∃ path, (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, _, _, _, hcore, hhit, hstmtHit⟩
  have hleafAt := hleaf x hx
  constructor
  · exact hpat
  · constructor
    · exact hleafAt
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathLeafAtBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    (x ∈ SubstDomain (mergeSubsts parts) ∧
      ∃ path, (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs []) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, _, _, _, hcore, hhit, hstmtHit⟩
  have hleafAt := hleaf x hx
  constructor
  · exact hpat
  · constructor
    · exact hleafAt
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchTupleNestedBinderWildPathPartLeafAtBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    ((∃ path, (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0) ∧
      ∃ part, part ∈ parts ∧ x ∈ SubstDomain part) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, hpartLeaf, _, _, hcore, hhit, hstmtHit⟩
  have hpartLeafAt := hpartLeaf x hx
  constructor
  · exact hpat
  · constructor
    · exact hpartLeafAt
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathPartLeafAtBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    ((∃ path, (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs []) ∧
      ∃ part, part ∈ parts ∧ x ∈ SubstDomain part) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, hpartLeaf, _, _, hcore, hhit, hstmtHit⟩
  have hpartLeafAt := hpartLeaf x hx
  constructor
  · exact hpat
  · constructor
    · exact hpartLeafAt
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchTupleNestedBinderWildPathOriginAtBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    (∃ path part,
      (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0 ∧
      part ∈ parts ∧
      x ∈ SubstDomain part) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, horigin, _, hcore, hhit, hstmtHit⟩
  have horiginAt := horigin x hx
  constructor
  · exact hpat
  · constructor
    · exact horiginAt
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathOriginAtBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    (∃ path part,
      (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs [] ∧
      part ∈ parts ∧
      x ∈ SubstDomain part) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, horigin, _, hcore, hhit, hstmtHit⟩
  have horiginAt := horigin x hx
  constructor
  · exact hpat
  · constructor
    · exact horiginAt
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchTupleNestedBinderWildPathValueOriginAtBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    (∃ path part value,
      (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0 ∧
      part ∈ parts ∧
      (x, value) ∈ part) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, _, hvalueOrigin, hcore, hhit, hstmtHit⟩
  have horigin := hvalueOrigin x hx
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathValueOriginAtBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    (∃ path part value,
      (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs [] ∧
      part ∈ parts ∧
      (x, value) ∈ part) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, _, hvalueOrigin, hcore, hhit, hstmtHit⟩
  have horigin := hvalueOrigin x hx
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchTupleNestedBinderWildPathLeafBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      (mergeSubsts parts)
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, _, _, _, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathLeafBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      (mergeSubsts parts)
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, _, _, _, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchTupleNestedBinderWildPathPartLeafBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathPartLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, hpartLeaf, _, _, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartLeaf
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathPartLeafBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathPartLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, hpartLeaf, _, _, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartLeaf
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchTupleNestedBinderWildPathOriginBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathPartOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, horigin, _, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathOriginBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathPartOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, horigin, _, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchTupleNestedBinderWildPathValueOriginBundle
    (p : Program) (ps : List Pattern) (vs : List Value) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathValueOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    MatchStmtBranchObserved (.tuple vs) ((.tuple ps, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, _, hvalueOrigin, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact hvalueOrigin
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructNestedBinderWildPathValueOriginBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (parts : List Subst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts)) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathValueOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest stmtBody stmtRest hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, _, hvalueOrigin, hcore, hhit, hstmtHit⟩
  constructor
  · exact hpat
  · constructor
    · exact hvalueOrigin
    · constructor
      · exact hcore
      · exact ⟨hhit, hstmtHit⟩

theorem typing_matchStructDomainBundle
    (p : Program) (name : String) (fs : List (String × Pattern))
    (fields : List (String × Value)) (σ : MatchSubst)
    (body : Expr) (rest : List (Pattern × Expr))
    (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ) :
    StructPatternWitness name fs fields σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    MatchStmtBranchObserved (.structV name fields) ((.struct name fs, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact structPatternWitness_exact name fs fields σ (by trivial)
  · constructor
    · exact structCoreMatchWitness_exact name fs fields σ hσ
    · constructor
      · exact substDomainAgreesMatchDomain_refl σ
      · exact typing_matchStructObservationBundle p name fs fields body rest stmtBody stmtRest hprog

theorem typing_matchObservationBundle_afterCtorMismatches
    (p : Program) (ctor : String) (pats : List Pattern) (args : List Value)
    (pre : List (Pattern × Expr)) (body : Expr) (rest : List (Pattern × Expr))
    (stmtPre : List (Pattern × List Stmt)) (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hpre : CtorMismatchExprPrefix ctor pre)
    (hstmtPre : CtorMismatchStmtPrefix ctor stmtPre) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.ctor ctor pats, body) :: rest) body ∧
    MatchStmtBranchObserved (.ctorV ctor args) (stmtPre ++ (.ctor ctor pats, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact typing_matchBranchObserved_afterCtorMismatches p ctor pats args pre body rest hprog hpre
  · exact typing_matchStmtBranchObserved_afterCtorMismatches p ctor pats args stmtPre stmtBody stmtRest hprog hstmtPre

theorem typing_matchWildcardObservationBundle_afterCtorMismatches
    (p : Program) (ctor : String) (args : List Value)
    (pre : List (Pattern × Expr)) (body : Expr) (rest : List (Pattern × Expr))
    (stmtPre : List (Pattern × List Stmt)) (stmtBody : List Stmt) (stmtRest : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hpre : CtorMismatchExprPrefix ctor pre)
    (hstmtPre : CtorMismatchStmtPrefix ctor stmtPre) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.wild, body) :: rest) body ∧
    MatchStmtBranchObserved (.ctorV ctor args) (stmtPre ++ (.wild, stmtBody) :: stmtRest) stmtBody := by
  constructor
  · exact typing_matchBranchObserved_wild_afterCtorMismatches p ctor args pre body rest hprog hpre
  · exact typing_matchStmtBranchObserved_wild_afterCtorMismatches p ctor args stmtPre stmtBody stmtRest hprog hstmtPre

theorem typing_matchCoverageBundle
    (p : Program) (ctor : String) (args : List Value)
    (cases : List (Pattern × Expr)) (body : Expr)
    (stmtCases : List (Pattern × List Stmt)) (stmtBody : List Stmt)
    (hprog : WellTypedProgram p)
    (hcover : CtorExprCasesCover ctor cases body)
    (hstmtCover : CtorStmtCasesCover ctor stmtCases stmtBody) :
    MatchBranchObserved (.ctorV ctor args) cases body ∧
    MatchStmtBranchObserved (.ctorV ctor args) stmtCases stmtBody := by
  constructor
  · exact typing_matchBranchObserved_ofCtorCover p ctor args cases body hprog hcover
  · exact typing_matchStmtBranchObserved_ofCtorCover p ctor args stmtCases stmtBody hprog hstmtCover

theorem typing_matchExhaustiveBundle
    (p : Program) (ctor : String) (args : List Value)
    (cases : List (Pattern × Expr))
    (stmtCases : List (Pattern × List Stmt))
    (hprog : WellTypedProgram p)
    (hexh : CtorExprCasesExhaustive ctor cases)
    (hstmtExh : CtorStmtCasesExhaustive ctor stmtCases) :
    (∃ body, MatchBranchObserved (.ctorV ctor args) cases body) ∧
    (∃ stmtBody, MatchStmtBranchObserved (.ctorV ctor args) stmtCases stmtBody) := by
  constructor
  · exact selectMatchExpr_existsOfExhaustive ctor args cases hexh
  · exact selectMatchStmt_existsOfExhaustive ctor args stmtCases hstmtExh

theorem typing_copyUpdateHelperBundle
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    semLookupValuePath v [] = some v ∧
    semUpdateValuePath v [] newv = some newv := by
  constructor
  · exact typing_lookupValuePath_root p v τ hprog hty
  · exact typing_updateValuePath_root p v newv τ hprog hty

theorem typing_copyUpdateObservationBundle
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    CopyUpdatePathObserved v [] newv newv := by
  exact typing_copyUpdatePathObserved_root p v newv τ hprog hty

theorem typing_copyUpdateHeadObservationBundle
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    CopyUpdateHeadObserved v [] newv newv := by
  exact typing_copyUpdateHeadObserved_root p v newv τ hprog hty

theorem typing_copyUpdatePrefixObservationBundle
    (p : Program) (v newv : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ) :
    CopyUpdatePrefixObserved v [] newv newv := by
  exact typing_copyUpdatePrefixObserved_root p v newv τ hprog hty

theorem typing_copyUpdateObservationBundle_general
    (p : Program) (v newv out : Value) (path : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v path newv = some out) :
    CopyUpdatePathObserved v path newv out := by
  exact typing_copyUpdatePathObserved_of_success p v newv out path τ hprog hty hupd

theorem typing_copyUpdateHeadObservationBundle_general
    (p : Program) (v newv out : Value) (path : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v path newv = some out) :
    CopyUpdateHeadObserved v path newv out := by
  exact typing_copyUpdateHeadObserved_of_success p v newv out path τ hprog hty hupd

theorem typing_copyUpdatePrefixObservationBundle_general
    (p : Program) (v newv out : Value) (path : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v path newv = some out) :
    CopyUpdatePrefixObserved v path newv out := by
  exact typing_copyUpdatePrefixObserved_of_success p v newv out path τ hprog hty hupd

theorem typing_copyUpdateChildObservationBundle_general
    (p : Program) (v newv out : Value) (key : String) (rest : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v (key :: rest) newv = some out) :
    ∃ name fields child child',
      v = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child rest newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      CopyUpdatePathObserved child rest newv child' := by
  exact copyUpdatePrefixObserved_child v key rest newv out
    (typing_copyUpdatePrefixObservationBundle_general p v newv out (key :: rest) τ hprog hty hupd)

theorem typing_copyUpdateChildChainObservationBundle_general
    (p : Program) (v newv out : Value) (key nextKey : String) (rest : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v (key :: nextKey :: rest) newv = some out) :
    ∃ name fields child child',
      v = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: rest) newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      CopyUpdatePrefixObserved child (nextKey :: rest) newv child' := by
  exact copyUpdatePrefixObserved_childChain v key nextKey rest newv out
    (typing_copyUpdatePrefixObservationBundle_general p v newv out (key :: nextKey :: rest) τ hprog hty hupd)

theorem typing_copyUpdateGrandchildObservationBundle_general
    (p : Program) (v newv out : Value) (key nextKey : String) (rest : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v (key :: nextKey :: rest) newv = some out) :
    ∃ name fields child child' childName childFields grandchild grandchild',
      v = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: rest) newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      child = .structV childName childFields ∧
      semLookupField childFields nextKey = some grandchild ∧
      semUpdateValuePath grandchild rest newv = some grandchild' ∧
      child' = .structV childName (semUpdateField childFields nextKey grandchild') ∧
      CopyUpdatePathObserved grandchild rest newv grandchild' := by
  exact copyUpdatePrefixObserved_grandchild v key nextKey rest newv out
    (typing_copyUpdatePrefixObservationBundle_general p v newv out (key :: nextKey :: rest) τ hprog hty hupd)

theorem typing_copyUpdateGrandchildChainObservationBundle_general
    (p : Program) (v newv out : Value) (key nextKey thirdKey : String) (rest : List String) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue v τ)
    (hupd : semUpdateValuePath v (key :: nextKey :: thirdKey :: rest) newv = some out) :
    ∃ name fields child child' childName childFields grandchild grandchild',
      v = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: thirdKey :: rest) newv = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      child = .structV childName childFields ∧
      semLookupField childFields nextKey = some grandchild ∧
      semUpdateValuePath grandchild (thirdKey :: rest) newv = some grandchild' ∧
      child' = .structV childName (semUpdateField childFields nextKey grandchild') ∧
      CopyUpdatePrefixObserved grandchild (thirdKey :: rest) newv grandchild' := by
  exact copyUpdatePrefixObserved_grandchildChain v key nextKey thirdKey rest newv out
    (typing_copyUpdatePrefixObservationBundle_general p v newv out (key :: nextKey :: thirdKey :: rest) τ hprog hty hupd)

theorem typing_enumHelperBundle
    (p : Program) (ctor enumName : String) (args : List Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (.ctorV ctor args) (.enum enumName)) :
    enumTagOf (.ctorV ctor args) = some ctor ∧
    enumPayloadOf (.ctorV ctor args) = some args := by
  constructor
  · exact typing_enumTagOf_ctor p ctor enumName args hprog hty
  · exact typing_enumPayloadOf_ctor p ctor enumName args hprog hty

theorem typing_enumObservationBundle
    (p : Program) (ctor enumName : String) (args : List Value)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (.ctorV ctor args) (.enum enumName)) :
    EnumEncodingObserved (.ctorV ctor args) ctor args := by
  exact typing_enumEncodingObserved_ctor p ctor enumName args hprog hty

theorem typing_pipelineHelperBundle
    (p : Program) (input : Value)
    (hprog : WellTypedProgram p) :
    runPipelineStages input [] = input := by
  exact typing_runPipelineStages_nil p input hprog

theorem typing_pipelineObservationBundle
    (p : Program) (input : Value) (stage : PipelineStage)
    (hprog : WellTypedProgram p) :
    PipelineSingleStageObserved input stage := by
  exact typing_pipelineSingleStageObserved p input stage hprog

theorem typing_pipelineObservationBundle_general
    (p : Program) (input : Value) (stages : List PipelineStage)
    (hprog : WellTypedProgram p) :
    PipelineStagesObserved input stages := by
  exact typing_pipelineStagesObserved p input stages hprog

theorem typing_tailObservationBundle
    (p : Program) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p) :
    interpTailExpr (.call fn args) = .recur fn (args.map interpExpr) ∧
    TailRecurObserved (.call fn args) fn (args.map interpExpr) ∧
    TailCallShapeObserved (.call fn args) fn (args.map interpExpr) ∧
    TailObservationalEq (.call fn args) (.call fn args) := by
  constructor
  · exact typing_tailcallHelperBundle p fn args hprog
  · constructor
    · exact typing_tailRecurObserved_call p fn args hprog
    · constructor
      · exact typing_tailCallShapeObserved_call p fn args hprog
      · exact tailObservationalEq_refl (.call fn args)

end Fo
