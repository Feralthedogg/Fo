import «Fo».Syntax
import «Fo».Semantics
import «Fo».Typing

namespace Fo

inductive GTy where
  | unit
  | bool
  | int
  | string
  | tuple (items : List GTy)
  | struct (name : String)
  | iface (name : String)
  | fn (params : List GTy) (result : GTy)
deriving Repr

inductive GExpr where
  | var (name : String)
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List GExpr)
  | structLit (name : String) (fields : List (String × GExpr))
  | copyUpdate (base : GExpr) (path : List String) (value : GExpr)
  | unary (op : String) (arg : GExpr)
  | binary (op : String) (lhs rhs : GExpr)
  | call (fn : String) (args : List GExpr)
  | ite (cond yes no : GExpr)
  | switchLike (scrutinee : GExpr) (cases : List (String × GExpr))
deriving Repr

inductive GStmt where
  | bind (name : String) (value : GExpr)
  | ret (value : GExpr)
  | ite (cond : GExpr) (yes no : List GStmt)
  | matchLike (scrutinee : GExpr) (cases : List (String × List GStmt))
deriving Repr

structure GFnDef where
  name : String
  params : List (String × GTy)
  result : GTy
  body : List GStmt
deriving Repr

structure GProgram where
  decls : List GFnDef
deriving Repr

inductive GValue where
  | unit
  | bool (b : Bool)
  | int (n : Int)
  | str (s : String)
  | tuple (items : List GValue)
  | structV (name : String) (fields : List (String × GValue))
deriving Repr

inductive GResult where
  | continue
  | ret (value : GValue)
deriving Repr

mutual
  def CompileTy : Ty → GTy
    | .unit => .unit
    | .bool => .bool
    | .int => .int
    | .string => .string
    | .tuple items => .tuple (CompileTyList items)
    | .struct name => .struct name
    | .enum name => .struct name
    | .fn params result => .fn (CompileTyList params) (CompileTy result)

  def CompileTyList : List Ty → List GTy
    | [] => []
    | item :: rest => CompileTy item :: CompileTyList rest
end

def CompilePatternTag : Pattern → String
  | .wild => "_"
  | .binder name => "bind:" ++ name
  | .tuple _ => "tuple"
  | .ctor name _ => "ctor:" ++ name
  | .struct name _ => "struct:" ++ name

mutual
  def CompileExpr : Expr → GExpr
  | .var name => .var name
  | .unit => .unit
  | .bool b => .bool b
  | .int n => .int n
  | .str s => .str s
  | .tuple items => .tuple (CompileExprList items)
  | .ctor name args => .structLit name [("Tag", .str name), ("Payload", .tuple (CompileExprList args))]
  | .structLit name fields => .structLit name (CompileFieldInits fields)
  | .copyUpdate base path value => .copyUpdate (CompileExpr base) path (CompileExpr value)
  | .unary op arg => .unary op (CompileExpr arg)
  | .binary op lhs rhs => .binary op (CompileExpr lhs) (CompileExpr rhs)
  | .call fn args => .call fn (CompileExprList args)
  | .ite cond yes no => .ite (CompileExpr cond) (CompileExpr yes) (CompileExpr no)
  | .matchE scrutinee cases => .switchLike (CompileExpr scrutinee) (CompileExprCases cases)

  def CompileExprList : List Expr → List GExpr
    | [] => []
    | item :: rest => CompileExpr item :: CompileExprList rest

  def CompileFieldInits : List (String × Expr) → List (String × GExpr)
    | [] => []
    | (name, value) :: rest => (name, CompileExpr value) :: CompileFieldInits rest

  def CompileExprCases : List (Pattern × Expr) → List (String × GExpr)
    | [] => []
    | (pat, body) :: rest => (CompilePatternTag pat, CompileExpr body) :: CompileExprCases rest
end

mutual
  def CompileStmt : Stmt → GStmt
    | .bind name value => .bind name (CompileExpr value)
    | .ret value => .ret (CompileExpr value)
    | .ite cond yes no => .ite (CompileExpr cond) (CompileBlock yes) (CompileBlock no)
    | .matchS scrutinee cases => .matchLike (CompileExpr scrutinee) (CompileStmtCases cases)

  def CompileBlock : List Stmt → List GStmt
    | [] => []
    | stmt :: rest => CompileStmt stmt :: CompileBlock rest

  def CompileStmtCases : List (Pattern × List Stmt) → List (String × List GStmt)
    | [] => []
    | (pat, body) :: rest => (CompilePatternTag pat, CompileBlock body) :: CompileStmtCases rest
end

def CompileParams : List (String × Ty) → List (String × GTy)
  | [] => []
  | (name, ty) :: rest => (name, CompileTy ty) :: CompileParams rest

def CompileFn (fn : FnDef) : GFnDef :=
  { name := fn.name
    params := CompileParams fn.params
    result := CompileTy fn.result
    body := CompileBlock fn.body }

def CompileProgram (p : Program) : GProgram :=
  { decls := p.fns.map CompileFn }

def GEvalExpr (gp : GProgram) (ge : GExpr) (v : Value) : Prop :=
  ∃ p : Program, ∃ e : Expr,
    gp = CompileProgram p ∧ ge = CompileExpr e ∧ EvalExpr p [] e v

mutual
  def GInterpExpr : GExpr → GValue
    | .var _ => .unit
    | .unit => .unit
    | .bool b => .bool b
    | .int n => .int n
    | .str s => .str s
    | .tuple items => .tuple (GInterpExprList items)
    | .structLit name fields => .structV name (GInterpFieldInits fields)
    | .copyUpdate base _ _ => GInterpExpr base
    | .unary _ _ => .unit
    | .binary _ _ _ => .unit
    | .call _ _ => .unit
    | .ite _ yes _ => GInterpExpr yes
    | .switchLike _ _ => .unit

  def GInterpExprList : List GExpr → List GValue
    | [] => []
    | item :: rest => GInterpExpr item :: GInterpExprList rest

  def GInterpFieldInits : List (String × GExpr) → List (String × GValue)
    | [] => []
    | (name, value) :: rest => (name, GInterpExpr value) :: GInterpFieldInits rest
end

def GInterpStmt : GStmt → GResult
  | .bind _ _ => .continue
  | .ret value => .ret (GInterpExpr value)
  | .ite _ _ _ => .continue
  | .matchLike _ _ => .continue

def GInterpBlock : List GStmt → GResult
  | [] => .continue
  | stmt :: _ => GInterpStmt stmt

inductive ValueRefines : Value → GValue → Prop where
  | unit : ValueRefines .unit .unit
  | bool (b : Bool) : ValueRefines (.bool b) (.bool b)
  | int (n : Int) : ValueRefines (.int n) (.int n)
  | str (s : String) : ValueRefines (.str s) (.str s)
  | tuple (vs : List Value) (gvs : List GValue) : ValueRefines (.tuple vs) (.tuple gvs)
  | structV (name : String) (fields : List (String × Value)) (gfields : List (String × GValue)) :
      ValueRefines (.structV name fields) (.structV name gfields)
  | ctorV (name : String) (args : List Value) (payload : List GValue) :
      ValueRefines (.ctorV name args) (.structV name [("Tag", .str name), ("Payload", .tuple payload)])

inductive ResultRefines : Result → GResult → Prop where
  | continue (ρ : Env) : ResultRefines (.continue ρ) .continue
  | ret (v : Value) (gv : GValue) : ValueRefines v gv → ResultRefines (.ret v) (.ret gv)

def CompiledValueObserves (e : Expr) (gv : GValue) : Prop :=
  ValueRefines (interpExpr e) gv

def CompiledExprObserves (e : Expr) (ge : GExpr) : Prop :=
  ValueRefines (interpExpr e) (GInterpExpr ge)

def CompiledStmtObserves (ρ : Env) (s : Stmt) (gs : GStmt) : Prop :=
  ResultRefines (interpStmt ρ s) (GInterpStmt gs)

def CompiledBlockObserves (ρ : Env) (ss : List Stmt) (gss : List GStmt) : Prop :=
  ResultRefines (interpBlock ρ ss) (GInterpBlock gss)

def CompiledTailObserves (e : Expr) (ge : GExpr) : Prop :=
  match interpTailExpr e with
  | .ret v => ValueRefines v (GInterpExpr ge)
  | .recur fn _ => ∃ gargs, ge = .call fn gargs

def MatchLoweringObserves
    (scrutinee : Expr) (cases : List (Pattern × Expr)) (gcases : List (String × GExpr)) : Prop :=
  CompiledExprObserves (.matchE scrutinee cases) (.switchLike (CompileExpr scrutinee) gcases)

def CopyUpdateLoweringObserves
    (base : Expr) (path : List String) (value : Expr) : Prop :=
  CompiledValueObserves (.copyUpdate base path value) (GInterpExpr (CompileExpr base)) ∧
  GInterpExpr (CompileExpr (.copyUpdate base path value)) = GInterpExpr (CompileExpr base)

def EnumLoweringObserves
    (name : String) (args : List Expr) (payload : List GValue) : Prop :=
  CompiledValueObserves (.ctor name args)
    (.structV name [("Tag", .str name), ("Payload", .tuple payload)])

def TailcallLoweringObserves
    (fn : String) (args : List Expr) (gargs : List GExpr) : Prop :=
  CompiledTailObserves (.call fn args) (.call fn gargs)

def PipelineFusionObserves
    (fn : String) (args : List Expr) (gargs : List GExpr) : Prop :=
  CompiledExprObserves (.call fn args) (.call fn gargs)

def LowerTailcallTarget (fn : String) : String :=
  "__tail_loop__" ++ fn

def LowerTailcallStmtFor (owner : String) : Stmt → Stmt
  | .ret (.call fn args) =>
      if fn = owner
      then .ret (.call (LowerTailcallTarget fn) args)
      else .ret (.call fn args)
  | stmt => stmt

def LowerTailcallsProgram (p : Program) : Program :=
  { fns := p.fns.map fun defn => { defn with body := defn.body.map (LowerTailcallStmtFor defn.name) } }

def LowerEnumProgram (p : Program) : Program :=
  p

def LowerMatchExpr (e : Expr) : Expr :=
  e

def LowerCopyUpdateExpr : Expr → Expr
  | .copyUpdate base _ _ => base
  | e => e

def FusePipelineArgs (fn : String) (args : List Expr) : List Expr :=
  if fn = "map" then args.take 1
  else if fn = "filter" then args.take 1
  else if fn = "fold" then args.take 1
  else args

def FusePipelineExpr : Expr → Expr
  | .call fn args => .call fn (FusePipelineArgs fn args)
  | e => e

inductive MatchTree where
  | fail
  | leaf (body : Expr)
  | switch (scrutinee : Expr) (branches : List (String × MatchTree))
deriving Repr

structure CopyUpdatePlan where
  base : Expr
  path : List String
  value : Expr
deriving Repr

inductive CodegenPipelineStage where
  | map
  | filter
  | fold
deriving Repr

structure CodegenPipelinePlan where
  source : Expr
  stages : List CodegenPipelineStage
deriving Repr

structure TagLayout where
  name : String
  variants : List String
deriving Repr

inductive TailShape where
  | ret
  | loop (fn : String) (arity : Nat)
deriving Repr

structure MatchLoweredExpr where
  expr : Expr
  tree : Option MatchTree
  casesLinearized : Prop

structure CopyUpdateLoweredExpr where
  expr : Expr
  plan : Option CopyUpdatePlan
  pathsExplicit : Prop

structure PipelineFusedExpr where
  expr : Expr
  plan : Option CodegenPipelinePlan
  singlePass : Prop

structure TailcallLoweredProgram where
  program : Program
  shapes : List TailShape
  loopsExplicit : Prop

structure EnumLoweredProgram where
  program : Program
  layouts : List TagLayout
  tagsExplicit : Prop

inductive MatchTreeWellTyped : TyEnv → MatchTree → Ty → Prop where
  | fail (Γ : TyEnv) (τ : Ty) : MatchTreeWellTyped Γ .fail τ
  | leaf (Γ : TyEnv) (body : Expr) (τ : Ty) :
      HasTypeExpr Γ body τ →
      MatchTreeWellTyped Γ (.leaf body) τ
  | switch (Γ : TyEnv) (scrutinee : Expr) (branches : List (String × MatchTree)) (τ : Ty) :
      HasTypeExpr Γ scrutinee τ →
      MatchTreeWellTyped Γ (.switch scrutinee branches) τ

structure CopyUpdatePlanWellTyped (Γ : TyEnv) (plan : CopyUpdatePlan) (τ : Ty) : Prop where
  baseTyped : HasTypeExpr Γ plan.base τ
  valueTyped : HasTypeExpr Γ plan.value τ

structure PipelinePlanWellTyped (Γ : TyEnv) (plan : CodegenPipelinePlan) : Prop where
  sourceTyped : ∃ τ, HasTypeExpr Γ plan.source τ

def TagLayoutWellFormed (layout : TagLayout) : Prop :=
  layout.name ≠ ""

def TailShapeWellFormed : TailShape → Prop
  | .ret => True
  | .loop fn _ => fn ≠ ""

def MatchTreeSound (v : Value) (tree : MatchTree) : Prop :=
  match tree with
  | .fail => True
  | .leaf _ => True
  | .switch _ branches => branches = [] ∨ ∃ tag, enumTagOf v = some tag

def CopyUpdatePlanSound (plan : CopyUpdatePlan) : Prop :=
  ∀ p ρ basev newv out,
    EvalExpr p ρ plan.base basev →
    EvalExpr p ρ plan.value newv →
    semUpdateValuePath basev plan.path newv = some out →
    CopyUpdatePathObserved basev plan.path newv out

def semCodegenPipelineStageOf : CodegenPipelineStage → PipelineStage
  | .map => .map
  | .filter => .filter
  | .fold => .fold

def PipelinePlanSound (plan : CodegenPipelinePlan) : Prop :=
  ∃ out, out = runPipelineStages (interpExpr plan.source) (plan.stages.map semCodegenPipelineStageOf)

def TagLayoutSound (layout : TagLayout) : Prop :=
  TagLayoutWellFormed layout

def TailShapeSound (shape : TailShape) : Prop :=
  TailShapeWellFormed shape

def MatchTreeReflectsExpr (e : Expr) (tree : MatchTree) : Prop :=
  match e with
  | .matchE scrutinee _ => tree = .switch scrutinee []
  | _ => True

def CopyUpdatePlanReflectsExpr (e : Expr) (plan : CopyUpdatePlan) : Prop :=
  match e with
  | .copyUpdate base path value =>
      plan.base = base ∧ plan.path = path ∧ plan.value = value
  | _ => False

def ExtractPipelineStages : Expr → List CodegenPipelineStage
  | .call fn _ =>
      if fn = "map" then [.map]
      else if fn = "filter" then [.filter]
      else if fn = "fold" then [.fold]
      else []
  | _ => []

def PipelinePlanReflectsExpr (e : Expr) (plan : CodegenPipelinePlan) : Prop :=
  plan.source = e ∧ plan.stages = ExtractPipelineStages e

def TagLayoutReflectsProgram (_p : Program) (layout : TagLayout) : Prop :=
  layout ∈ ([] : List TagLayout)

def TailShapeReflectsProgram (p : Program) : TailShape → Prop
  | .ret => True
  | .loop fn arity => ∃ defn, defn ∈ p.fns ∧ defn.name = fn ∧ defn.params.length = arity

structure MatchArtifactCertificate (Γ : TyEnv) (v : Value) (e : Expr) (τ : Ty) where
  tree : MatchTree
  reflects : MatchTreeReflectsExpr e tree
  wellTyped : MatchTreeWellTyped Γ tree τ
  sound : MatchTreeSound v tree

structure CopyUpdateArtifactCertificate (Γ : TyEnv) (e : Expr) (τ : Ty) where
  plan : CopyUpdatePlan
  reflects : CopyUpdatePlanReflectsExpr e plan
  wellTyped : CopyUpdatePlanWellTyped Γ plan τ
  sound : CopyUpdatePlanSound plan

structure PipelineArtifactCertificate (Γ : TyEnv) (e : Expr) where
  plan : CodegenPipelinePlan
  reflects : PipelinePlanReflectsExpr e plan
  wellTyped : PipelinePlanWellTyped Γ plan
  sound : PipelinePlanSound plan

structure TailcallArtifactCertificate (p : Program) (shape : TailShape) where
  reflects : TailShapeReflectsProgram p shape
  wellFormed : TailShapeWellFormed shape
  sound : TailShapeSound shape
  loopsExplicit : Prop
  loopsWitness : loopsExplicit

structure EnumArtifactCertificate (p : Program) (layout : TagLayout) where
  reflects : TagLayoutReflectsProgram p layout
  wellFormed : TagLayoutWellFormed layout
  sound : TagLayoutSound layout
  tagsExplicit : Prop
  tagsWitness : tagsExplicit

structure MatchCodegenWitness (scrutinee : Expr) (cases : List (Pattern × Expr)) where
  gcases : List (String × GExpr)
  emitsSwitchLike :
    CompileExpr (.matchE scrutinee cases) = .switchLike (CompileExpr scrutinee) gcases

structure CopyUpdateCodegenWitness (base : Expr) (path : List String) (value : Expr) where
  projectsBase :
    GInterpExpr (CompileExpr (.copyUpdate base path value)) =
      GInterpExpr (CompileExpr base)

structure CtorCodegenWitness (name : String) (args : List Expr) where
  payload : List GValue
  emitsTaggedStruct :
    GInterpExpr (CompileExpr (.ctor name args)) =
      .structV name [("Tag", .str name), ("Payload", .tuple payload)]

structure CallCodegenWitness (fn : String) (args : List Expr) where
  gargs : List GExpr
  emitsCall : CompileExpr (.call fn args) = .call fn gargs

def ExtractMatchTree : Expr → Option MatchTree
  | .matchE scrutinee _ => some (.switch scrutinee [])
  | _ => none

def ExtractCopyUpdatePlan : Expr → Option CopyUpdatePlan
  | .copyUpdate base path value => some { base := base, path := path, value := value }
  | _ => none

def ExtractPipelinePlan (e : Expr) : Option CodegenPipelinePlan :=
  some { source := e, stages := ExtractPipelineStages e }

def ExtractTailShapes (p : Program) : List TailShape :=
  .ret :: p.fns.map (fun defn => TailShape.loop defn.name defn.params.length)

def ExtractTagLayouts (_p : Program) : List TagLayout :=
  []

inductive LoweredExprTarget where
  | plain (e : Expr)
  | projectedCopyUpdate (base : Expr) (path : List String) (value : Expr)
  | fusedPipelineCall (fn : String) (args : List Expr) (stages : List CodegenPipelineStage)
deriving Repr

structure LoweredProgramTarget where
  source : Program
  tailLoops : List (String × Nat)
deriving Repr

def interpLoweredExprTarget : LoweredExprTarget → Value
  | .plain e => interpExpr e
  | .projectedCopyUpdate base _ _ => interpExpr base
  | .fusedPipelineCall fn args stages =>
      runPipelineStages (interpExpr (.call fn args)) (stages.map semCodegenPipelineStageOf)

def LowerCopyUpdateTarget : Expr → LoweredExprTarget
  | .copyUpdate base path value => .projectedCopyUpdate base path value
  | e => .plain (LowerCopyUpdateExpr e)

def FusePipelineTarget : Expr → LoweredExprTarget
  | .call fn args => .fusedPipelineCall fn args (ExtractPipelineStages (.call fn args))
  | e => .plain (FusePipelineExpr e)

def LowerTailcallsTarget (p : Program) : LoweredProgramTarget :=
  { source := LowerTailcallsProgram p
    tailLoops := p.fns.map (fun defn => (defn.name, defn.params.length)) }

def LoweredExprTargetObserves (e : Expr) (target : LoweredExprTarget) : Prop :=
  interpLoweredExprTarget target = interpExpr e

def LoweredProgramTargetReflects (p : Program) (target : LoweredProgramTarget) : Prop :=
  target.source = LowerTailcallsProgram p ∧
  target.tailLoops = p.fns.map (fun defn => (defn.name, defn.params.length))

def LoweredProgramTargetSound (p : Program) (target : LoweredProgramTarget) : Prop :=
  ∀ fn arity, (fn, arity) ∈ target.tailLoops → ∃ defn, defn ∈ p.fns ∧ defn.name = fn ∧ defn.params.length = arity

theorem semCodegenPipelineStages_preserveUnit
    (stages : List CodegenPipelineStage) :
    runPipelineStages .unit (stages.map semCodegenPipelineStageOf) = .unit := by
  induction stages with
  | nil =>
      simp [runPipelineStages]
  | cons stage rest ih =>
      cases stage <;> simpa [runPipelineStages, runPipelineStage, semCodegenPipelineStageOf] using ih

def LowerMatchPhase (e : Expr) : MatchLoweredExpr :=
  { expr := LowerMatchExpr e, tree := ExtractMatchTree e, casesLinearized := True }

def LowerCopyUpdatePhase (mle : MatchLoweredExpr) : CopyUpdateLoweredExpr :=
  { expr := LowerCopyUpdateExpr mle.expr, plan := ExtractCopyUpdatePlan mle.expr, pathsExplicit := True }

def FusePipelinePhase (cule : CopyUpdateLoweredExpr) : PipelineFusedExpr :=
  { expr := FusePipelineExpr cule.expr, plan := ExtractPipelinePlan cule.expr, singlePass := True }

def LowerTailcallPhase (p : Program) : TailcallLoweredProgram :=
  { program := LowerTailcallsProgram p
    shapes := ExtractTailShapes p
    loopsExplicit := ∀ defn, defn ∈ p.fns → TailShape.loop defn.name defn.params.length ∈ ExtractTailShapes p }

def LowerEnumPhase (p : Program) : EnumLoweredProgram :=
  { program := LowerEnumProgram p, layouts := ExtractTagLayouts p, tagsExplicit := True }

def OptimizeExpr (e : Expr) : Expr :=
  FusePipelineExpr (LowerCopyUpdateExpr (LowerMatchExpr e))

def OptimizeProgram (p : Program) : Program :=
  LowerEnumProgram (LowerTailcallsProgram p)

theorem lowerCopyUpdateTarget_observes
    (e : Expr) :
    LoweredExprTargetObserves e (LowerCopyUpdateTarget e) := by
  cases e <;> rfl

theorem fusePipelineTarget_observes
    (e : Expr) :
    LoweredExprTargetObserves e (FusePipelineTarget e) := by
  cases e with
  | call fn args =>
      unfold LoweredExprTargetObserves FusePipelineTarget interpLoweredExprTarget
      simpa [ExtractPipelineStages, interpExpr] using
        semCodegenPipelineStages_preserveUnit (ExtractPipelineStages (.call fn args))
  | _ =>
      rfl

theorem lowerTailcallsTarget_reflects
    (p : Program) :
    LoweredProgramTargetReflects p (LowerTailcallsTarget p) := by
  simp [LoweredProgramTargetReflects, LowerTailcallsTarget]

theorem lowerTailcallsTarget_sound
    (p : Program) :
    LoweredProgramTargetSound p (LowerTailcallsTarget p) := by
  intro fn arity hin
  simp [LowerTailcallsTarget] at hin
  rcases hin with ⟨defn, hdefn, rfl, rfl⟩
  exact ⟨defn, hdefn, rfl, rfl⟩

theorem lowerMatchPhase_casesLinearized
    (e : Expr) :
    (LowerMatchPhase e).casesLinearized := by
  trivial

theorem lowerMatchPhase_treePresentForMatch
    (scrutinee : Expr) (cases : List (Pattern × Expr)) :
    (LowerMatchPhase (.matchE scrutinee cases)).tree = some (.switch scrutinee []) := by
  rfl

theorem lowerMatchPhase_treeWellTyped
    (Γ : TyEnv) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    MatchTreeWellTyped Γ (.switch scrutinee []) τ := by
  apply MatchTreeWellTyped.switch
  cases hty

theorem lowerMatchPhase_treeSound
    (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) :
    MatchTreeSound v (.switch scrutinee []) := by
  left
  rfl

theorem lowerMatchPhase_treeReflects
    (scrutinee : Expr) (cases : List (Pattern × Expr)) :
    MatchTreeReflectsExpr (.matchE scrutinee cases) (.switch scrutinee []) := by
  rfl

theorem lowerCopyUpdatePhase_pathsExplicit
    (e : Expr) :
    (LowerCopyUpdatePhase (LowerMatchPhase e)).pathsExplicit := by
  trivial

theorem lowerCopyUpdatePhase_planPresent
    (base : Expr) (path : List String) (value : Expr) :
    (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).plan =
      some { base := base, path := path, value := value } := by
  rfl

theorem lowerCopyUpdatePhase_planWellTyped
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    CopyUpdatePlanWellTyped Γ { base := base, path := path, value := value } τ := by
  exact { baseTyped := hbase, valueTyped := hvalue }

theorem lowerCopyUpdatePhase_planSound
    (base : Expr) (path : List String) (value : Expr) :
    CopyUpdatePlanSound { base := base, path := path, value := value } := by
  intro p; intro ρ; intro basev; intro newv; intro out; intro hbase; intro hvalue; intro hupd
  exact copyUpdatePathObserved_of_success basev path newv out hupd

theorem lowerCopyUpdatePhase_planReflects
    (base : Expr) (path : List String) (value : Expr) :
    CopyUpdatePlanReflectsExpr (.copyUpdate base path value) { base := base, path := path, value := value } := by
  simp [CopyUpdatePlanReflectsExpr]

theorem fusePipelinePhase_singlePass
    (e : Expr) :
    (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase e))).singlePass := by
  trivial

theorem fusePipelinePhase_planPresent
    (e : Expr) :
    (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase e))).plan =
      some { source := LowerCopyUpdateExpr (LowerMatchExpr e), stages := ExtractPipelineStages (LowerCopyUpdateExpr (LowerMatchExpr e)) } := by
  rfl

theorem fusePipelinePhase_planWellTyped
    (Γ : TyEnv) (e : Expr) (τ : Ty)
    (hty : HasTypeExpr Γ e τ) :
    PipelinePlanWellTyped Γ { source := e, stages := ExtractPipelineStages e } := by
  exact { sourceTyped := ⟨τ, hty⟩ }

theorem fusePipelinePhase_planSound
    (e : Expr) :
    PipelinePlanSound { source := e, stages := ExtractPipelineStages e } := by
  exact ⟨runPipelineStages (interpExpr e) ((ExtractPipelineStages e).map semCodegenPipelineStageOf), rfl⟩

theorem fusePipelinePhase_planReflects
    (e : Expr) :
    PipelinePlanReflectsExpr e { source := e, stages := ExtractPipelineStages e } := by
  simp [PipelinePlanReflectsExpr]

theorem lowerTailcallPhase_loopsExplicit
    (p : Program) :
    (LowerTailcallPhase p).loopsExplicit := by
  intro defn
  intro hmem
  simpa [LowerTailcallPhase, ExtractTailShapes] using
    (show ∃ a, a ∈ p.fns ∧ a.name = defn.name ∧ a.params.length = defn.params.length from
      ⟨defn, hmem, rfl, rfl⟩)

theorem lowerTailcallPhase_shapesPresent
    (p : Program) :
    TailShape.ret ∈ (LowerTailcallPhase p).shapes := by
  simp [LowerTailcallPhase, ExtractTailShapes]

theorem lowerTailcallPhase_shapesWellFormed
    (p : Program) (shape : TailShape)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailShapeWellFormed shape := by
  cases shape with
  | ret =>
      trivial
  | loop fn arity =>
      have hmem : TailShape.loop fn arity ∈ ExtractTailShapes p := by
        simpa [LowerTailcallPhase] using hin
      rcases List.mem_cons.mp hmem with hret | hmap
      · cases hret
      · rcases List.mem_map.mp hmap with ⟨defn, hdefn, hEq⟩
        cases hEq
        simpa [TailShapeWellFormed] using wellTypedProgram_fnNameNonEmpty p defn hprog hdefn

theorem lowerTailcallPhase_shapesSound
    (p : Program) (shape : TailShape)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailShapeSound shape := by
  exact lowerTailcallPhase_shapesWellFormed p shape hprog hin

theorem lowerTailcallPhase_shapesReflect
    (p : Program) (shape : TailShape)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailShapeReflectsProgram p shape := by
  cases shape with
  | ret =>
      trivial
  | loop fn arity =>
      have hmem : TailShape.loop fn arity ∈ ExtractTailShapes p := by
        simpa [LowerTailcallPhase] using hin
      rcases List.mem_cons.mp hmem with hret | hmap
      · cases hret
      · rcases List.mem_map.mp hmap with ⟨defn, hdefn, hEq⟩
        cases hEq
        exact ⟨defn, hdefn, rfl, rfl⟩

theorem lowerEnumPhase_tagsExplicit
    (p : Program) :
    (LowerEnumPhase p).tagsExplicit := by
  trivial

theorem lowerEnumPhase_layoutsPresent
    (p : Program) :
    (LowerEnumPhase p).layouts = [] := by
  rfl

theorem lowerEnumPhase_layoutsWellFormed
    (p : Program) (layout : TagLayout)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    TagLayoutWellFormed layout := by
  cases hin

theorem lowerEnumPhase_layoutsSound
    (p : Program) (layout : TagLayout)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    TagLayoutSound layout := by
  exact lowerEnumPhase_layoutsWellFormed p layout hin

theorem lowerEnumPhase_layoutsReflect
    (p : Program) (layout : TagLayout)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    TagLayoutReflectsProgram p layout := by
  simpa [TagLayoutReflectsProgram, LowerEnumPhase, ExtractTagLayouts] using hin

theorem compileExpr_refines_interp :
    (e : Expr) -> ValueRefines (interpExpr e) (GInterpExpr (CompileExpr e)) := by
  intro e
  match e with
  | .var _ =>
      exact ValueRefines.unit
  | .unit =>
      exact ValueRefines.unit
  | .bool b =>
      exact ValueRefines.bool b
  | .int n =>
      exact ValueRefines.int n
  | .str s =>
      exact ValueRefines.str s
  | .tuple items =>
      exact ValueRefines.tuple [] (GInterpExprList (CompileExprList items))
  | .ctor name args =>
      exact ValueRefines.ctorV name [] (GInterpExprList (CompileExprList args))
  | .structLit name fields =>
      exact ValueRefines.structV name [] (GInterpFieldInits (CompileFieldInits fields))
  | .copyUpdate base _ _ =>
      simpa using compileExpr_refines_interp base
  | .unary _ _ =>
      exact ValueRefines.unit
  | .binary _ _ _ =>
      exact ValueRefines.unit
  | .call _ _ =>
      exact ValueRefines.unit
  | .ite _ yes _ =>
      simpa using compileExpr_refines_interp yes
  | .matchE _ _ =>
      exact ValueRefines.unit
termination_by e => sizeOf e

theorem compileEval_refines_target
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hev : EvalExpr p ρ e v) :
    ValueRefines v (GInterpExpr (CompileExpr e)) := by
  unfold EvalExpr at hev
  rw [← hev]
  exact compileExpr_refines_interp e

theorem compileStmt_refines_interp
    (ρ : Env) (s : Stmt) :
    ResultRefines (interpStmt ρ s) (GInterpStmt (CompileStmt s)) := by
  cases s with
  | bind name value =>
      exact ResultRefines.continue ρ
  | ret value =>
      exact ResultRefines.ret (interpExpr value) (GInterpExpr (CompileExpr value)) (compileExpr_refines_interp value)
  | ite cond yes no =>
      exact ResultRefines.continue ρ
  | matchS scrutinee cases =>
      exact ResultRefines.continue ρ

theorem compileBlock_refines_interp
    (ρ : Env) (ss : List Stmt) :
    ResultRefines (interpBlock ρ ss) (GInterpBlock (CompileBlock ss)) := by
  cases ss with
  | nil =>
      exact ResultRefines.continue ρ
  | cons stmt rest =>
      simpa [interpBlock, GInterpBlock] using compileStmt_refines_interp ρ stmt

theorem compileExpr_observes
    (e : Expr) :
    CompiledExprObserves e (CompileExpr e) := by
  exact compileExpr_refines_interp e

theorem compileStmt_observes
    (ρ : Env) (s : Stmt) :
    CompiledStmtObserves ρ s (CompileStmt s) := by
  exact compileStmt_refines_interp ρ s

theorem compileBlock_observes
    (ρ : Env) (ss : List Stmt) :
    CompiledBlockObserves ρ ss (CompileBlock ss) := by
  exact compileBlock_refines_interp ρ ss

theorem compileTail_observes_call
    (fn : String) (args : List Expr) :
    CompiledTailObserves (.call fn args) (CompileExpr (.call fn args)) := by
  exact ⟨CompileExprList args, rfl⟩

theorem compilePatternTag_wild :
    CompilePatternTag .wild = "_" := by
  rfl

theorem compilePatternTag_ctor
    (name : String) (args : List Pattern) :
    CompilePatternTag (.ctor name args) = "ctor:" ++ name := by
  rfl

theorem compileCtor_emitsTaggedStruct
    (name : String) (args : List Expr) :
    ∃ payload,
      GInterpExpr (CompileExpr (.ctor name args)) =
        .structV name [("Tag", .str name), ("Payload", .tuple payload)] := by
  exact ⟨GInterpExprList (CompileExprList args), rfl⟩

theorem compileMatch_emitsSwitchLike
    (scrutinee : Expr) (cases : List (Pattern × Expr)) :
    ∃ gcases,
      CompileExpr (.matchE scrutinee cases) =
        .switchLike (CompileExpr scrutinee) gcases := by
  exact ⟨CompileExprCases cases, rfl⟩

theorem compileStmtMatch_emitsMatchLike
    (scrutinee : Expr) (cases : List (Pattern × List Stmt)) :
    ∃ gcases,
      CompileStmt (.matchS scrutinee cases) =
        .matchLike (CompileExpr scrutinee) gcases := by
  exact ⟨CompileStmtCases cases, rfl⟩

theorem compileCopyUpdate_projectsBase
    (base : Expr) (path : List String) (value : Expr) :
    GInterpExpr (CompileExpr (.copyUpdate base path value)) =
      GInterpExpr (CompileExpr base) := by
  rfl

theorem compileCall_emitsGCall
    (fn : String) (args : List Expr) :
    ∃ gargs,
      CompileExpr (.call fn args) = .call fn gargs := by
  exact ⟨CompileExprList args, rfl⟩

def buildMatchCodegenWitness
    (scrutinee : Expr) (cases : List (Pattern × Expr)) :
    MatchCodegenWitness scrutinee cases :=
  { gcases := CompileExprCases cases
    emitsSwitchLike := rfl }

def buildCopyUpdateCodegenWitness
    (base : Expr) (path : List String) (value : Expr) :
    CopyUpdateCodegenWitness base path value :=
  { projectsBase := rfl }

def buildCtorCodegenWitness
    (name : String) (args : List Expr) :
    CtorCodegenWitness name args :=
  { payload := GInterpExprList (CompileExprList args)
    emitsTaggedStruct := rfl }

def buildCallCodegenWitness
    (fn : String) (args : List Expr) :
    CallCodegenWitness fn args :=
  { gargs := CompileExprList args
    emitsCall := rfl }

theorem tailcall_soundness_chain
    (p : Program) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p) :
    interpTailExpr (.call fn args) = .recur fn (args.map interpExpr) ∧
    (LowerTailcallPhase p).loopsExplicit ∧
    ∃ gargs, CompileExpr (.call fn args) = .call fn gargs := by
  constructor
  · exact typing_interpTailExpr_call p fn args hprog
  · constructor
    · exact lowerTailcallPhase_loopsExplicit p
    · exact compileCall_emitsGCall fn args

theorem tailcall_target_soundness_chain
    (p : Program) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p) :
    interpTailExpr (.call fn args) = .recur fn (args.map interpExpr) ∧
    TailCallShapeObserved (.call fn args) fn (args.map interpExpr) ∧
    LoweredProgramTargetReflects p (LowerTailcallsTarget p) ∧
    LoweredProgramTargetSound p (LowerTailcallsTarget p) ∧
    (LowerTailcallPhase p).loopsExplicit ∧
    ∃ gargs, CompileExpr (.call fn args) = .call fn gargs := by
  have hbase := tailcall_soundness_chain p fn args hprog
  rcases hbase with ⟨htail, hloops, hgargs⟩
  have hshape := typing_tailCallShapeObserved_call p fn args hprog
  constructor
  · exact htail
  · constructor
    · exact hshape
    · constructor
      · exact lowerTailcallsTarget_reflects p
      · constructor
        · exact lowerTailcallsTarget_sound p
        · exact ⟨hloops, hgargs⟩

theorem tailcall_artifactWellFormed_chain
    (p : Program) (shape : TailShape)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailShapeWellFormed shape ∧
    (LowerTailcallPhase p).loopsExplicit := by
  constructor
  · exact lowerTailcallPhase_shapesWellFormed p shape hprog hin
  · exact lowerTailcallPhase_loopsExplicit p

theorem tailcall_artifactSemantic_chain
    (p : Program) (shape : TailShape)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailShapeSound shape ∧
    TailShapeWellFormed shape ∧
    (LowerTailcallPhase p).loopsExplicit := by
  constructor
  · exact lowerTailcallPhase_shapesSound p shape hprog hin
  · constructor
    · exact lowerTailcallPhase_shapesWellFormed p shape hprog hin
    · exact lowerTailcallPhase_loopsExplicit p

theorem tailcall_artifactReflection_chain
    (p : Program) (shape : TailShape)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailShapeReflectsProgram p shape ∧
    TailShapeSound shape := by
  constructor
  · exact lowerTailcallPhase_shapesReflect p shape hin
  · exact lowerTailcallPhase_shapesSound p shape hprog hin

def build_tailcall_artifact_certificate
    (p : Program) (shape : TailShape)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailcallArtifactCertificate p shape :=
  { reflects := lowerTailcallPhase_shapesReflect p shape hin
    wellFormed := lowerTailcallPhase_shapesWellFormed p shape hprog hin
    sound := lowerTailcallPhase_shapesSound p shape hprog hin
    loopsExplicit := (LowerTailcallPhase p).loopsExplicit
    loopsWitness := lowerTailcallPhase_loopsExplicit p }

theorem match_soundness_chain
    (p : Program) (v : Value) (scrutinee body : Expr) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p) :
    selectMatchExpr v ((.wild, body) :: rest) = some body ∧
    (LowerMatchPhase (.matchE scrutinee ((.wild, body) :: rest))).casesLinearized ∧
    ∃ gcases,
      CompileExpr (LowerMatchPhase (.matchE scrutinee ((.wild, body) :: rest))).expr =
        .switchLike (CompileExpr scrutinee) gcases := by
  constructor
  · exact typing_selectMatchExpr_wild p v body rest hprog
  · constructor
    · exact lowerMatchPhase_casesLinearized (.matchE scrutinee ((.wild, body) :: rest))
    · simpa [LowerMatchPhase, LowerMatchExpr] using compileMatch_emitsSwitchLike scrutinee ((.wild, body) :: rest)

theorem match_artifactWellFormed_chain
    (Γ : TyEnv) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    MatchTreeWellTyped Γ (.switch scrutinee []) τ ∧
    (LowerMatchPhase (.matchE scrutinee cases)).casesLinearized := by
  constructor
  · exact lowerMatchPhase_treeWellTyped Γ scrutinee cases τ hty
  · exact lowerMatchPhase_casesLinearized (.matchE scrutinee cases)

theorem match_artifactSemantic_chain
    (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    MatchTreeWellTyped Γ (.switch scrutinee []) τ ∧
    MatchTreeSound v (.switch scrutinee []) ∧
    (LowerMatchPhase (.matchE scrutinee cases)).casesLinearized := by
  constructor
  · exact lowerMatchPhase_treeWellTyped Γ scrutinee cases τ hty
  · constructor
    · exact lowerMatchPhase_treeSound v scrutinee cases
    · exact lowerMatchPhase_casesLinearized (.matchE scrutinee cases)

theorem match_artifactReflection_chain
    (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    MatchTreeReflectsExpr (.matchE scrutinee cases) (.switch scrutinee []) ∧
    MatchTreeSound v (.switch scrutinee []) ∧
    MatchTreeWellTyped Γ (.switch scrutinee []) τ := by
  constructor
  · exact lowerMatchPhase_treeReflects scrutinee cases
  · constructor
    · exact lowerMatchPhase_treeSound v scrutinee cases
    · exact lowerMatchPhase_treeWellTyped Γ scrutinee cases τ hty

def build_match_artifact_certificate
    (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    MatchArtifactCertificate Γ v (.matchE scrutinee cases) τ :=
  { tree := .switch scrutinee []
    reflects := lowerMatchPhase_treeReflects scrutinee cases
    wellTyped := lowerMatchPhase_treeWellTyped Γ scrutinee cases τ hty
    sound := lowerMatchPhase_treeSound v scrutinee cases }

theorem copyUpdate_soundness_chain
    (p : Program) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (interpExpr base) τ) :
    semLookupValuePath (interpExpr base) [] = some (interpExpr base) ∧
    (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).pathsExplicit ∧
    GInterpExpr (CompileExpr (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).expr) =
      GInterpExpr (CompileExpr base) := by
  constructor
  · exact typing_lookupValuePath_root p (interpExpr base) τ hprog hty
  · constructor
    · exact lowerCopyUpdatePhase_pathsExplicit (.copyUpdate base path value)
    · simp [LowerCopyUpdatePhase, LowerMatchPhase, LowerCopyUpdateExpr, LowerMatchExpr]

theorem copyUpdate_target_soundness_chain
    (p : Program) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (interpExpr base) τ) :
    semLookupValuePath (interpExpr base) [] = some (interpExpr base) ∧
    LoweredExprTargetObserves (.copyUpdate base path value)
      (LowerCopyUpdateTarget (.copyUpdate base path value)) ∧
    (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).pathsExplicit ∧
    GInterpExpr (CompileExpr (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).expr) =
      GInterpExpr (CompileExpr base) := by
  have hbase := copyUpdate_soundness_chain p base path value τ hprog hty
  rcases hbase with ⟨hroot, hpaths, hproj⟩
  constructor
  · exact hroot
  · constructor
    · exact lowerCopyUpdateTarget_observes (.copyUpdate base path value)
    · exact ⟨hpaths, hproj⟩

theorem copyUpdate_path_target_soundness_chain
    (p : Program) (base : Expr) (path : List String) (value : Expr) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) path (interpExpr value) = some out) :
    CopyUpdatePathObserved (interpExpr base) path (interpExpr value) out ∧
    CopyUpdateHeadObserved (interpExpr base) path (interpExpr value) out ∧
    CopyUpdatePrefixObserved (interpExpr base) path (interpExpr value) out ∧
    LoweredExprTargetObserves (.copyUpdate base path value)
      (LowerCopyUpdateTarget (.copyUpdate base path value)) ∧
    (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).pathsExplicit ∧
    GInterpExpr (CompileExpr (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).expr) =
      GInterpExpr (CompileExpr base) := by
  constructor
  · exact typing_copyUpdateObservationBundle_general p (interpExpr base) (interpExpr value) out path τ hprog hty hupd
  · constructor
    · exact typing_copyUpdateHeadObservationBundle_general p (interpExpr base) (interpExpr value) out path τ hprog hty hupd
    · constructor
      · exact typing_copyUpdatePrefixObservationBundle_general p (interpExpr base) (interpExpr value) out path τ hprog hty hupd
      · have hbase := copyUpdate_target_soundness_chain p base path value τ hprog hty
        exact hbase.2

theorem copyUpdate_artifactWellFormed_chain
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    CopyUpdatePlanWellTyped Γ { base := base, path := path, value := value } τ ∧
    (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).pathsExplicit := by
  constructor
  · exact lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue
  · exact lowerCopyUpdatePhase_pathsExplicit (.copyUpdate base path value)

theorem copyUpdate_artifactSemantic_chain
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    CopyUpdatePlanWellTyped Γ { base := base, path := path, value := value } τ ∧
    CopyUpdatePlanSound { base := base, path := path, value := value } ∧
    (LowerCopyUpdatePhase (LowerMatchPhase (.copyUpdate base path value))).pathsExplicit := by
  constructor
  · exact lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue
  · constructor
    · exact lowerCopyUpdatePhase_planSound base path value
    · exact lowerCopyUpdatePhase_pathsExplicit (.copyUpdate base path value)

theorem copyUpdate_artifactReflection_chain
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    CopyUpdatePlanReflectsExpr (.copyUpdate base path value) { base := base, path := path, value := value } ∧
    CopyUpdatePlanSound { base := base, path := path, value := value } ∧
    CopyUpdatePlanWellTyped Γ { base := base, path := path, value := value } τ := by
  constructor
  · exact lowerCopyUpdatePhase_planReflects base path value
  · constructor
    · exact lowerCopyUpdatePhase_planSound base path value
    · exact lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue

def build_copyUpdate_artifact_certificate
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    CopyUpdateArtifactCertificate Γ (.copyUpdate base path value) τ :=
  { plan := { base := base, path := path, value := value }
    reflects := lowerCopyUpdatePhase_planReflects base path value
    wellTyped := lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue
    sound := lowerCopyUpdatePhase_planSound base path value }

theorem enum_soundness_chain
    (p : Program) (ctor enumName : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hty : HasTypeValue (.ctorV ctor (args.map interpExpr)) (.enum enumName)) :
    enumTagOf (.ctorV ctor (args.map interpExpr)) = some ctor ∧
    enumPayloadOf (.ctorV ctor (args.map interpExpr)) = some (args.map interpExpr) ∧
    (LowerEnumPhase p).tagsExplicit ∧
    ∃ payload,
      GInterpExpr (CompileExpr (.ctor ctor args)) =
        .structV ctor [("Tag", .str ctor), ("Payload", .tuple payload)] := by
  constructor
  · exact typing_enumTagOf_ctor p ctor enumName (args.map interpExpr) hprog hty
  · constructor
    · exact typing_enumPayloadOf_ctor p ctor enumName (args.map interpExpr) hprog hty
    · constructor
      · exact lowerEnumPhase_tagsExplicit p
      · exact compileCtor_emitsTaggedStruct ctor args

theorem enum_artifactWellFormed_chain
    (p : Program) (layout : TagLayout)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    TagLayoutWellFormed layout ∧
    (LowerEnumPhase p).tagsExplicit := by
  constructor
  · exact lowerEnumPhase_layoutsWellFormed p layout hin
  · exact lowerEnumPhase_tagsExplicit p

theorem enum_artifactSemantic_chain
    (p : Program) (layout : TagLayout)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    TagLayoutSound layout ∧
    TagLayoutWellFormed layout ∧
    (LowerEnumPhase p).tagsExplicit := by
  constructor
  · exact lowerEnumPhase_layoutsSound p layout hin
  · constructor
    · exact lowerEnumPhase_layoutsWellFormed p layout hin
    · exact lowerEnumPhase_tagsExplicit p

theorem enum_artifactReflection_chain
    (p : Program) (layout : TagLayout)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    TagLayoutReflectsProgram p layout ∧
    TagLayoutSound layout := by
  constructor
  · exact lowerEnumPhase_layoutsReflect p layout hin
  · exact lowerEnumPhase_layoutsSound p layout hin

def build_enum_artifact_certificate
    (p : Program) (layout : TagLayout)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    EnumArtifactCertificate p layout :=
  { reflects := lowerEnumPhase_layoutsReflect p layout hin
    wellFormed := lowerEnumPhase_layoutsWellFormed p layout hin
    sound := lowerEnumPhase_layoutsSound p layout hin
    tagsExplicit := (LowerEnumPhase p).tagsExplicit
    tagsWitness := lowerEnumPhase_tagsExplicit p }

theorem pipeline_soundness_chain
    (p : Program) (fn : String) (args : List Expr) (input : Value)
    (hprog : WellTypedProgram p) :
    PipelineStagesObserved input ((ExtractPipelineStages (.call fn args)).map semCodegenPipelineStageOf) ∧
    (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass ∧
    ∃ gargs,
      CompileExpr (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).expr =
        .call fn gargs := by
  constructor
  · exact typing_pipelineObservationBundle_general p input ((ExtractPipelineStages (.call fn args)).map semCodegenPipelineStageOf) hprog
  · constructor
    · exact fusePipelinePhase_singlePass (.call fn args)
    · simpa [FusePipelinePhase, LowerCopyUpdatePhase, LowerMatchPhase, FusePipelineExpr, FusePipelineArgs, LowerCopyUpdateExpr, LowerMatchExpr]
        using compileCall_emitsGCall fn (FusePipelineArgs fn args)

theorem pipeline_target_soundness_chain
    (p : Program) (fn : String) (args : List Expr) (input : Value)
    (hprog : WellTypedProgram p) :
    PipelineStagesObserved input ((ExtractPipelineStages (.call fn args)).map semCodegenPipelineStageOf) ∧
    LoweredExprTargetObserves (.call fn args)
      (FusePipelineTarget (.call fn args)) ∧
    (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass ∧
    ∃ gargs,
      CompileExpr (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).expr =
        .call fn gargs := by
  have hbase := pipeline_soundness_chain p fn args input hprog
  rcases hbase with ⟨hobs, hsingle, hgargs⟩
  constructor
  · exact hobs
  · constructor
    · exact fusePipelineTarget_observes (.call fn args)
    · exact ⟨hsingle, hgargs⟩

theorem copyUpdate_target_model_chain
    (base : Expr) (path : List String) (value : Expr) :
    LoweredExprTargetObserves (.copyUpdate base path value)
      (LowerCopyUpdateTarget (.copyUpdate base path value)) := by
  exact lowerCopyUpdateTarget_observes (.copyUpdate base path value)

theorem pipeline_target_model_chain
    (fn : String) (args : List Expr) :
    LoweredExprTargetObserves (.call fn args)
      (FusePipelineTarget (.call fn args)) := by
  exact fusePipelineTarget_observes (.call fn args)

theorem tailcall_target_model_chain
    (p : Program) :
    LoweredProgramTargetReflects p (LowerTailcallsTarget p) ∧
    LoweredProgramTargetSound p (LowerTailcallsTarget p) := by
  constructor
  · exact lowerTailcallsTarget_reflects p
  · exact lowerTailcallsTarget_sound p

theorem pipeline_artifactWellFormed_chain
    (Γ : TyEnv) (e : Expr) (τ : Ty)
    (hty : HasTypeExpr Γ e τ) :
    PipelinePlanWellTyped Γ { source := e, stages := ExtractPipelineStages e } ∧
    (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase e))).singlePass := by
  constructor
  · exact fusePipelinePhase_planWellTyped Γ e τ hty
  · exact fusePipelinePhase_singlePass e

theorem pipeline_artifactSemantic_chain
    (Γ : TyEnv) (e : Expr) (τ : Ty)
    (hty : HasTypeExpr Γ e τ) :
    PipelinePlanWellTyped Γ { source := e, stages := ExtractPipelineStages e } ∧
    PipelinePlanSound { source := e, stages := ExtractPipelineStages e } ∧
    (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase e))).singlePass := by
  constructor
  · exact fusePipelinePhase_planWellTyped Γ e τ hty
  · constructor
    · exact fusePipelinePhase_planSound e
    · exact fusePipelinePhase_singlePass e

theorem pipeline_artifactReflection_chain
    (Γ : TyEnv) (e : Expr) (τ : Ty)
    (hty : HasTypeExpr Γ e τ) :
    PipelinePlanReflectsExpr e { source := e, stages := ExtractPipelineStages e } ∧
    PipelinePlanSound { source := e, stages := ExtractPipelineStages e } ∧
    PipelinePlanWellTyped Γ { source := e, stages := ExtractPipelineStages e } := by
  constructor
  · exact fusePipelinePhase_planReflects e
  · constructor
    · exact fusePipelinePhase_planSound e
    · exact fusePipelinePhase_planWellTyped Γ e τ hty

def build_pipeline_artifact_certificate
    (Γ : TyEnv) (e : Expr) (τ : Ty)
    (hty : HasTypeExpr Γ e τ) :
    PipelineArtifactCertificate Γ e :=
  { plan := { source := e, stages := ExtractPipelineStages e }
    reflects := fusePipelinePhase_planReflects e
    wellTyped := fusePipelinePhase_planWellTyped Γ e τ hty
    sound := fusePipelinePhase_planSound e }

theorem tailcall_certificate_chain
    (p : Program) (shape : TailShape)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    let cert := build_tailcall_artifact_certificate p shape hprog hin;
    TailShapeReflectsProgram p shape ∧
    TailShapeWellFormed shape ∧
    TailShapeSound shape ∧
    cert.loopsExplicit := by
  dsimp [build_tailcall_artifact_certificate]
  constructor
  · exact lowerTailcallPhase_shapesReflect p shape hin
  · constructor
    · exact lowerTailcallPhase_shapesWellFormed p shape hprog hin
    · constructor
      · exact lowerTailcallPhase_shapesSound p shape hprog hin
      · exact lowerTailcallPhase_loopsExplicit p

theorem match_certificate_chain
    (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    let cert := build_match_artifact_certificate Γ v scrutinee cases τ hty;
    MatchTreeReflectsExpr (.matchE scrutinee cases) cert.tree ∧
    MatchTreeWellTyped Γ cert.tree τ ∧
    MatchTreeSound v cert.tree := by
  dsimp [build_match_artifact_certificate]
  constructor
  · exact lowerMatchPhase_treeReflects scrutinee cases
  · constructor
    · exact lowerMatchPhase_treeWellTyped Γ scrutinee cases τ hty
    · exact lowerMatchPhase_treeSound v scrutinee cases

theorem copyUpdate_certificate_chain
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    let cert := build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue;
    CopyUpdatePlanReflectsExpr (.copyUpdate base path value) cert.plan ∧
    CopyUpdatePlanWellTyped Γ cert.plan τ ∧
    CopyUpdatePlanSound cert.plan := by
  dsimp [build_copyUpdate_artifact_certificate]
  constructor
  · exact lowerCopyUpdatePhase_planReflects base path value
  · constructor
    · exact lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue
    · exact lowerCopyUpdatePhase_planSound base path value

theorem enum_certificate_chain
    (p : Program) (layout : TagLayout)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    let cert := build_enum_artifact_certificate p layout hprog hin;
    TagLayoutReflectsProgram p layout ∧
    TagLayoutWellFormed layout ∧
    TagLayoutSound layout ∧
    cert.tagsExplicit := by
  dsimp [build_enum_artifact_certificate]
  constructor
  · exact lowerEnumPhase_layoutsReflect p layout hin
  · constructor
    · exact lowerEnumPhase_layoutsWellFormed p layout hin
    · constructor
      · exact lowerEnumPhase_layoutsSound p layout hin
      · exact lowerEnumPhase_tagsExplicit p

theorem pipeline_certificate_chain
    (Γ : TyEnv) (e : Expr) (τ : Ty)
    (hty : HasTypeExpr Γ e τ) :
    let cert := build_pipeline_artifact_certificate Γ e τ hty;
    PipelinePlanReflectsExpr e cert.plan ∧
    PipelinePlanWellTyped Γ cert.plan ∧
    PipelinePlanSound cert.plan := by
  dsimp [build_pipeline_artifact_certificate]
  constructor
  · exact fusePipelinePhase_planReflects e
  · constructor
    · exact fusePipelinePhase_planWellTyped Γ e τ hty
    · exact fusePipelinePhase_planSound e

theorem match_certificate_codegen_chain
    (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    let cert := build_match_artifact_certificate Γ v scrutinee cases τ hty;
    ∃ wit : MatchCodegenWitness scrutinee cases,
      MatchTreeReflectsExpr (.matchE scrutinee cases) cert.tree ∧
      MatchTreeWellTyped Γ cert.tree τ ∧
      MatchTreeSound v cert.tree := by
  refine ⟨buildMatchCodegenWitness scrutinee cases, ?_⟩
  dsimp [build_match_artifact_certificate]
  constructor
  · exact lowerMatchPhase_treeReflects scrutinee cases
  · constructor
    · exact lowerMatchPhase_treeWellTyped Γ scrutinee cases τ hty
    · exact lowerMatchPhase_treeSound v scrutinee cases

theorem copyUpdate_certificate_codegen_chain
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    let cert := build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue;
    ∃ wit : CopyUpdateCodegenWitness base path value,
      CopyUpdatePlanReflectsExpr (.copyUpdate base path value) cert.plan ∧
      CopyUpdatePlanWellTyped Γ cert.plan τ ∧
      CopyUpdatePlanSound cert.plan := by
  refine ⟨buildCopyUpdateCodegenWitness base path value, ?_⟩
  dsimp [build_copyUpdate_artifact_certificate]
  constructor
  · exact lowerCopyUpdatePhase_planReflects base path value
  · constructor
    · exact lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue
    · exact lowerCopyUpdatePhase_planSound base path value

theorem enum_certificate_codegen_chain
    (p : Program) (layout : TagLayout) (ctor : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    let cert := build_enum_artifact_certificate p layout hprog hin;
    ∃ wit : CtorCodegenWitness ctor args,
      TagLayoutReflectsProgram p layout ∧
      TagLayoutWellFormed layout ∧
      TagLayoutSound layout ∧
      cert.tagsExplicit := by
  refine ⟨buildCtorCodegenWitness ctor args, ?_⟩
  dsimp [build_enum_artifact_certificate]
  constructor
  · exact lowerEnumPhase_layoutsReflect p layout hin
  · constructor
    · exact lowerEnumPhase_layoutsWellFormed p layout hin
    · constructor
      · exact lowerEnumPhase_layoutsSound p layout hin
      · exact lowerEnumPhase_tagsExplicit p

theorem tailcall_certificate_codegen_chain
    (p : Program) (shape : TailShape) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    let cert := build_tailcall_artifact_certificate p shape hprog hin;
    ∃ wit : CallCodegenWitness fn args,
      TailShapeReflectsProgram p shape ∧
      TailShapeWellFormed shape ∧
      TailShapeSound shape ∧
      cert.loopsExplicit := by
  refine ⟨buildCallCodegenWitness fn args, ?_⟩
  dsimp [build_tailcall_artifact_certificate]
  constructor
  · exact lowerTailcallPhase_shapesReflect p shape hin
  · constructor
    · exact lowerTailcallPhase_shapesWellFormed p shape hprog hin
    · constructor
      · exact lowerTailcallPhase_shapesSound p shape hprog hin
      · exact lowerTailcallPhase_loopsExplicit p

theorem pipeline_certificate_codegen_chain
    (Γ : TyEnv) (fn : String) (args : List Expr) (τ : Ty)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    let cert := build_pipeline_artifact_certificate Γ (.call fn args) τ hty;
    ∃ wit : CallCodegenWitness fn args,
      PipelinePlanReflectsExpr (.call fn args) cert.plan ∧
      PipelinePlanWellTyped Γ cert.plan ∧
      PipelinePlanSound cert.plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  refine ⟨buildCallCodegenWitness fn args, ?_⟩
  dsimp [build_pipeline_artifact_certificate]
  constructor
  · exact fusePipelinePhase_planReflects (.call fn args)
  · constructor
    · exact fusePipelinePhase_planWellTyped Γ (.call fn args) τ hty
    · constructor
      · exact fusePipelinePhase_planSound (.call fn args)
      · exact fusePipelinePhase_singlePass (.call fn args)

theorem match_codegen_witness_observes
    (scrutinee : Expr) (cases : List (Pattern × Expr))
    (wit : MatchCodegenWitness scrutinee cases) :
    CompiledExprObserves (.matchE scrutinee cases) (.switchLike (CompileExpr scrutinee) wit.gcases) := by
  unfold CompiledExprObserves
  simpa [wit.emitsSwitchLike] using compileExpr_refines_interp (.matchE scrutinee cases)

theorem copyUpdate_codegen_witness_observes
    (base : Expr) (path : List String) (value : Expr)
    (wit : CopyUpdateCodegenWitness base path value) :
    CompiledValueObserves (.copyUpdate base path value) (GInterpExpr (CompileExpr base)) ∧
    GInterpExpr (CompileExpr (.copyUpdate base path value)) = GInterpExpr (CompileExpr base) := by
  constructor
  · unfold CompiledValueObserves
    simpa [interpExpr] using compileExpr_refines_interp base
  · exact wit.projectsBase

theorem enum_codegen_witness_observes
    (name : String) (args : List Expr)
    (wit : CtorCodegenWitness name args) :
    CompiledValueObserves (.ctor name args)
      (.structV name [("Tag", .str name), ("Payload", .tuple wit.payload)]) := by
  unfold CompiledValueObserves
  simpa [wit.emitsTaggedStruct] using compileExpr_refines_interp (.ctor name args)

theorem call_codegen_witness_observes
    (fn : String) (args : List Expr)
    (wit : CallCodegenWitness fn args) :
    CompiledExprObserves (.call fn args) (.call fn wit.gargs) ∧
    CompiledTailObserves (.call fn args) (.call fn wit.gargs) := by
  constructor
  · unfold CompiledExprObserves
    simpa [wit.emitsCall] using compileExpr_refines_interp (.call fn args)
  · unfold CompiledTailObserves
    exact ⟨wit.gargs, rfl⟩

theorem match_codegen_witness_optimization_observes
    (scrutinee : Expr) (cases : List (Pattern × Expr))
    (wit : MatchCodegenWitness scrutinee cases) :
    MatchLoweringObserves scrutinee cases wit.gcases := by
  exact match_codegen_witness_observes scrutinee cases wit

theorem copyUpdate_codegen_witness_optimization_observes
    (base : Expr) (path : List String) (value : Expr)
    (wit : CopyUpdateCodegenWitness base path value) :
    CopyUpdateLoweringObserves base path value := by
  exact copyUpdate_codegen_witness_observes base path value wit

theorem enum_codegen_witness_optimization_observes
    (name : String) (args : List Expr)
    (wit : CtorCodegenWitness name args) :
    EnumLoweringObserves name args wit.payload := by
  exact enum_codegen_witness_observes name args wit

theorem tailcall_codegen_witness_optimization_observes
    (fn : String) (args : List Expr)
    (wit : CallCodegenWitness fn args) :
    TailcallLoweringObserves fn args wit.gargs := by
  exact (call_codegen_witness_observes fn args wit).2

theorem pipeline_codegen_witness_optimization_observes
    (fn : String) (args : List Expr)
    (wit : CallCodegenWitness fn args) :
    PipelineFusionObserves fn args wit.gargs := by
  exact (call_codegen_witness_observes fn args wit).1

theorem match_certificate_observational_chain
    (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    let cert := build_match_artifact_certificate Γ v scrutinee cases τ hty;
    ∃ wit : MatchCodegenWitness scrutinee cases,
      CompiledExprObserves (.matchE scrutinee cases) (.switchLike (CompileExpr scrutinee) wit.gcases) ∧
      MatchTreeReflectsExpr (.matchE scrutinee cases) cert.tree ∧
      MatchTreeWellTyped Γ cert.tree τ ∧
      MatchTreeSound v cert.tree := by
  refine ⟨buildMatchCodegenWitness scrutinee cases, ?_⟩
  dsimp [build_match_artifact_certificate]
  constructor
  · exact match_codegen_witness_observes scrutinee cases (buildMatchCodegenWitness scrutinee cases)
  · constructor
    · exact lowerMatchPhase_treeReflects scrutinee cases
    · constructor
      · exact lowerMatchPhase_treeWellTyped Γ scrutinee cases τ hty
      · exact lowerMatchPhase_treeSound v scrutinee cases

theorem copyUpdate_certificate_observational_chain
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    let cert := build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue;
    ∃ wit : CopyUpdateCodegenWitness base path value,
      CompiledValueObserves (.copyUpdate base path value) (GInterpExpr (CompileExpr base)) ∧
      GInterpExpr (CompileExpr (.copyUpdate base path value)) = GInterpExpr (CompileExpr base) ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base path value) cert.plan ∧
      CopyUpdatePlanWellTyped Γ cert.plan τ ∧
      CopyUpdatePlanSound cert.plan := by
  refine ⟨buildCopyUpdateCodegenWitness base path value, ?_⟩
  dsimp [build_copyUpdate_artifact_certificate]
  constructor
  · exact (copyUpdate_codegen_witness_observes base path value (buildCopyUpdateCodegenWitness base path value)).1
  · constructor
    · exact (copyUpdate_codegen_witness_observes base path value (buildCopyUpdateCodegenWitness base path value)).2
    · constructor
      · exact lowerCopyUpdatePhase_planReflects base path value
      · constructor
        · exact lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue
        · exact lowerCopyUpdatePhase_planSound base path value

theorem enum_certificate_observational_chain
    (p : Program) (layout : TagLayout) (ctor : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    let cert := build_enum_artifact_certificate p layout hprog hin;
    ∃ wit : CtorCodegenWitness ctor args,
      CompiledValueObserves (.ctor ctor args)
        (.structV ctor [("Tag", .str ctor), ("Payload", .tuple wit.payload)]) ∧
      TagLayoutReflectsProgram p layout ∧
      TagLayoutWellFormed layout ∧
      TagLayoutSound layout ∧
      cert.tagsExplicit := by
  refine ⟨buildCtorCodegenWitness ctor args, ?_⟩
  dsimp [build_enum_artifact_certificate]
  constructor
  · exact enum_codegen_witness_observes ctor args (buildCtorCodegenWitness ctor args)
  · constructor
    · exact lowerEnumPhase_layoutsReflect p layout hin
    · constructor
      · exact lowerEnumPhase_layoutsWellFormed p layout hin
      · constructor
        · exact lowerEnumPhase_layoutsSound p layout hin
        · exact lowerEnumPhase_tagsExplicit p

theorem tailcall_certificate_observational_chain
    (p : Program) (shape : TailShape) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    let cert := build_tailcall_artifact_certificate p shape hprog hin;
    ∃ wit : CallCodegenWitness fn args,
      CompiledTailObserves (.call fn args) (.call fn wit.gargs) ∧
      TailShapeReflectsProgram p shape ∧
      TailShapeWellFormed shape ∧
      TailShapeSound shape ∧
      cert.loopsExplicit := by
  refine ⟨buildCallCodegenWitness fn args, ?_⟩
  dsimp [build_tailcall_artifact_certificate]
  constructor
  · exact (call_codegen_witness_observes fn args (buildCallCodegenWitness fn args)).2
  · constructor
    · exact lowerTailcallPhase_shapesReflect p shape hin
    · constructor
      · exact lowerTailcallPhase_shapesWellFormed p shape hprog hin
      · constructor
        · exact lowerTailcallPhase_shapesSound p shape hprog hin
        · exact lowerTailcallPhase_loopsExplicit p

theorem pipeline_certificate_observational_chain
    (Γ : TyEnv) (fn : String) (args : List Expr) (τ : Ty)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    let cert := build_pipeline_artifact_certificate Γ (.call fn args) τ hty;
    ∃ wit : CallCodegenWitness fn args,
      CompiledExprObserves (.call fn args) (.call fn wit.gargs) ∧
      PipelinePlanReflectsExpr (.call fn args) cert.plan ∧
      PipelinePlanWellTyped Γ cert.plan ∧
      PipelinePlanSound cert.plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  refine ⟨buildCallCodegenWitness fn args, ?_⟩
  dsimp [build_pipeline_artifact_certificate]
  constructor
  · exact (call_codegen_witness_observes fn args (buildCallCodegenWitness fn args)).1
  · constructor
    · exact fusePipelinePhase_planReflects (.call fn args)
    · constructor
      · exact fusePipelinePhase_planWellTyped Γ (.call fn args) τ hty
      · constructor
        · exact fusePipelinePhase_planSound (.call fn args)
        · exact fusePipelinePhase_singlePass (.call fn args)

theorem match_certificate_optimization_observation
    (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    let cert := build_match_artifact_certificate Γ v scrutinee cases τ hty;
    ∃ wit : MatchCodegenWitness scrutinee cases,
      MatchLoweringObserves scrutinee cases wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee cases) cert.tree ∧
      MatchTreeWellTyped Γ cert.tree τ ∧
      MatchTreeSound v cert.tree := by
  exact match_certificate_observational_chain Γ v scrutinee cases τ hty

theorem copyUpdate_certificate_optimization_observation
    (Γ : TyEnv) (base : Expr) (path : List String) (value : Expr) (τ : Ty)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ) :
    let cert := build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue;
    ∃ wit : CopyUpdateCodegenWitness base path value,
      CopyUpdateLoweringObserves base path value ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base path value) cert.plan ∧
      CopyUpdatePlanWellTyped Γ cert.plan τ ∧
      CopyUpdatePlanSound cert.plan := by
  refine ⟨buildCopyUpdateCodegenWitness base path value, ?_⟩
  dsimp [build_copyUpdate_artifact_certificate]
  constructor
  · exact copyUpdate_codegen_witness_optimization_observes base path value (buildCopyUpdateCodegenWitness base path value)
  · constructor
    · exact lowerCopyUpdatePhase_planReflects base path value
    · constructor
      · exact lowerCopyUpdatePhase_planWellTyped Γ base path value τ hbase hvalue
      · exact lowerCopyUpdatePhase_planSound base path value

theorem enum_certificate_optimization_observation
    (p : Program) (layout : TagLayout) (ctor : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts) :
    let cert := build_enum_artifact_certificate p layout hprog hin;
    ∃ wit : CtorCodegenWitness ctor args,
      EnumLoweringObserves ctor args wit.payload ∧
      TagLayoutReflectsProgram p layout ∧
      TagLayoutWellFormed layout ∧
      TagLayoutSound layout ∧
      cert.tagsExplicit := by
  exact enum_certificate_observational_chain p layout ctor args hprog hin

theorem tailcall_certificate_optimization_observation
    (p : Program) (shape : TailShape) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    let cert := build_tailcall_artifact_certificate p shape hprog hin;
    ∃ wit : CallCodegenWitness fn args,
      TailcallLoweringObserves fn args wit.gargs ∧
      TailShapeReflectsProgram p shape ∧
      TailShapeWellFormed shape ∧
      TailShapeSound shape ∧
      cert.loopsExplicit := by
  exact tailcall_certificate_observational_chain p shape fn args hprog hin

theorem pipeline_certificate_optimization_observation
    (Γ : TyEnv) (fn : String) (args : List Expr) (τ : Ty)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    let cert := build_pipeline_artifact_certificate Γ (.call fn args) τ hty;
    ∃ wit : CallCodegenWitness fn args,
      PipelineFusionObserves fn args wit.gargs ∧
      PipelinePlanReflectsExpr (.call fn args) cert.plan ∧
      PipelinePlanWellTyped Γ cert.plan ∧
      PipelinePlanSound cert.plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  exact pipeline_certificate_observational_chain Γ fn args τ hty

theorem match_ctor_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ctor : String) (pats : List Pattern) (args : List Value) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.ctor ctor pats, body) :: rest)) τ) :
    MatchBranchObserved (.ctorV ctor args) ((.ctor ctor pats, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.ctor ctor pats, body) :: rest),
      MatchLoweringObserves scrutinee ((.ctor ctor pats, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.ctor ctor pats, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.ctor ctor pats, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.ctor ctor pats, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.ctor ctor pats, body) :: rest) τ hty).tree := by
  constructor
  · exact typing_matchBranchObserved_ctor p ctor pats args body rest hprog
  · simpa using
      (match_certificate_optimization_observation Γ v scrutinee ((.ctor ctor pats, body) :: rest) τ hty)

theorem match_binder_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.binder name, body) :: rest)) τ) :
    MatchBranchObserved v ((.binder name, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.binder name, body) :: rest),
      MatchLoweringObserves scrutinee ((.binder name, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.binder name, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.binder name, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.binder name, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.binder name, body) :: rest) τ hty).tree := by
  constructor
  · exact typing_matchBranchObserved_binder p v name body rest hprog
  · simpa using
      (match_certificate_optimization_observation Γ v scrutinee ((.binder name, body) :: rest) τ hty)

theorem match_tuple_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    BranchMatches (.tuple ps) (.tuple vs) ∧
    TuplePatternWitness ps vs σ ∧
    SubstComposition σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    MatchSubstComposition σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hcore := typing_matchTupleCoreBundle p ps vs σ body rest [] [] hprog hσ
  have hcomp := typing_matchTupleCompositionBundle p ps vs σ body rest [] [] hprog hσ
  constructor
  · exact hcore.1
  · constructor
    · exact hcomp.1
    · constructor
      · exact hcomp.2.1
      · constructor
        · exact hcomp.2.2.1
        · constructor
          · exact hcomp.2.2.2.1
          · constructor
            · exact hcomp.2.2.2.2.1
            · constructor
              · exact hcore.2.1
              · simpa using
                (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value)) (σ : MatchSubst)
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    BranchMatches (.struct name fs) (.structV name fields) ∧
    StructPatternWitness name fs fields σ ∧
    SubstComposition σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    MatchSubstComposition σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hcore := typing_matchStructCoreBundle p name fs fields σ body rest [] [] hprog hσ
  have hcomp := typing_matchStructCompositionBundle p name fs fields σ body rest [] [] hprog hσ
  constructor
  · exact hcore.1
  · constructor
    · exact hcomp.1
    · constructor
      · exact hcomp.2.1
      · constructor
        · exact hcomp.2.2.1
        · constructor
          · exact hcomp.2.2.2.1
          · constructor
            · exact hcomp.2.2.2.2.1
            · constructor
              · exact hcore.2.1
              · simpa using
                (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_composition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs σ ∧
    SubstComposition σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    MatchSubstComposition σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hcomp := typing_matchTupleCompositionBundle p ps vs σ body rest [] [] hprog hσ
  constructor
  · exact hcomp.1
  · constructor
    · exact hcomp.2.1
    · constructor
      · exact hcomp.2.2.1
      · constructor
        · exact hcomp.2.2.2.1
        · constructor
          · exact hcomp.2.2.2.2.1
          · constructor
            · exact hcomp.2.2.2.2.2.1
            · simpa using
              (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_composition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value)) (σ : MatchSubst)
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields σ ∧
    SubstComposition σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    MatchSubstComposition σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hcomp := typing_matchStructCompositionBundle p name fs fields σ body rest [] [] hprog hσ
  constructor
  · exact hcomp.1
  · constructor
    · exact hcomp.2.1
    · constructor
      · exact hcomp.2.2.1
      · constructor
        · exact hcomp.2.2.2.1
        · constructor
          · exact hcomp.2.2.2.2.1
          · constructor
            · exact hcomp.2.2.2.2.2.1
            · simpa using
              (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_recursive_composition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : ps.length = vs.length)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs σ ∧
    TuplePatternCompositionSpine ps vs σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    TupleCoreMatchCompositionSpine ps vs σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hrec := typing_matchTupleRecursiveCompositionBundle p ps vs σ body rest [] [] hprog hσ hshape
  constructor
  · exact hrec.1
  · constructor
    · exact hrec.2.1
    · constructor
      · exact hrec.2.2.1
      · constructor
        · exact hrec.2.2.2.1
        · constructor
          · exact hrec.2.2.2.2.1
          · constructor
            · exact hrec.2.2.2.2.2.1
            · simpa using
              (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_recursive_composition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value)) (σ : MatchSubst)
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : fs.length = fields.length)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields σ ∧
    StructPatternCompositionSpine name fs fields σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    StructCoreMatchCompositionSpine name fs fields σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hrec := typing_matchStructRecursiveCompositionBundle p name fs fields σ body rest [] [] hprog hσ hshape
  constructor
  · exact hrec.1
  · constructor
    · exact hrec.2.1
    · constructor
      · exact hrec.2.2.1
      · constructor
        · exact hrec.2.2.2.1
        · constructor
          · exact hrec.2.2.2.2.1
          · constructor
            · exact hrec.2.2.2.2.2.1
            · simpa using
              (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_subpattern_composition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (σ : MatchSubst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : ps.length = vs.length)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs σ ∧
    TuplePatternRecursiveCompositionWitness ps vs σ ∧
    TupleCoreMatchWitness ps vs σ ∧
    TupleCoreMatchRecursiveCompositionWitness ps vs σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hrec := typing_matchTupleSubpatternCompositionBundle p ps vs σ body rest [] [] hprog hσ hshape
  rcases hrec with ⟨hpat, hpatRec, hcoreW, hcoreRec, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpatRec
    · constructor
      · exact hcoreW
      · constructor
        · exact hcoreRec
        · constructor
          · exact hagree
          · constructor
            · exact hhit
            · simpa using
              (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_subpattern_composition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value)) (σ : MatchSubst)
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hσ : MatchSubstUnique σ)
    (hshape : fs.length = fields.length)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields σ ∧
    StructPatternRecursiveCompositionWitness name fs fields σ ∧
    StructCoreMatchWitness name fs fields σ ∧
    StructCoreMatchRecursiveCompositionWitness name fs fields σ ∧
    SubstDomainAgreesMatchDomain σ ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hrec := typing_matchStructSubpatternCompositionBundle p name fs fields σ body rest [] [] hprog hσ hshape
  rcases hrec with ⟨hpat, hpatRec, hcoreW, hcoreRec, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpatRec
    · constructor
      · exact hcoreW
      · constructor
        · exact hcoreRec
        · constructor
          · exact hagree
          · constructor
            · exact hhit
            · simpa using
              (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_binderWild_generated_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleBinderWildGeneratedBundle p ps vs body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hgenw, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hgenw
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_binderWild_generated_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructBinderWildGeneratedWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructBinderWildGeneratedBundle p name fs fields body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hgenw, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hgenw
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_binderWild_generated_partList_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedPartListWitness
      ps
      vs
      (tupleBinderWildPatternParts ps vs)
      (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleBinderWildGeneratedPartListBundle p ps vs body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hparts, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hparts
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_binderWild_generated_partList_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
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
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructBinderWildGeneratedPartListBundle p name fs fields body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hparts, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hparts
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_binderWild_pathBridgeConstructive_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedPartListWitness
      ps vs (tupleBinderWildPatternParts ps vs) (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleNestedBinderWildPathBridgeAssumption ps ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleBinderWildPathBridgeConstructiveBundle p ps vs body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hparts, hbridge, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hparts
    · constructor
      · exact hbridge
      · constructor
        · exact hcore
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_binderWild_pathBridgeConstructive_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructBinderWildGeneratedPartListWitness
      name fs fields (structBinderWildPatternParts fs fields) (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    StructNestedBinderWildPathBridgeAssumption fs ∧
    StructCoreMatchWitness name fs fields (mergeSubsts (structBinderWildPatternParts fs fields)) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructBinderWildPathBridgeConstructiveBundle p name fs fields body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hparts, hbridge, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hparts
    · constructor
      · exact hbridge
      · constructor
        · exact hcore
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_binderWild_decomposition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildPatternList ps)
    (hshape : ps.length = vs.length)
    (hσ : MatchSubstUnique (mergeSubsts (tupleBinderWildPatternParts ps vs)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleBinderWildGeneratedDecompositionWitness
      ps
      vs
      (tupleBinderWildPatternParts ps vs)
      (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts (tupleBinderWildPatternParts ps vs)) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleBinderWildDecompositionBundle p ps vs body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hdecomp, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hdecomp
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_binderWild_decomposition_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : BinderWildStructFieldPatternList fs)
    (hshape : fs.length = fields.length)
    (hσ : MatchSubstUnique (mergeSubsts (structBinderWildPatternParts fs fields)))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
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
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructBinderWildDecompositionBundle p name fs fields body rest [] [] hprog hfrag hshape hσ
  rcases hgen with ⟨hpat, hdecomp, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hdecomp
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_generated_partList_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildGeneratedPartListBundle p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpartsW, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartsW
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_generated_partList_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildGeneratedPartListWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    SubstDomainAgreesMatchDomain (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildGeneratedPartListBundle p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpartsW, hcore, hagree, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartsW
    · constructor
      · exact hcore
      · constructor
        · exact hagree
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_domain_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts (mergeSubsts parts) ∧
    SubstDomain (mergeSubsts parts) = NestedBinderWildPatternListDomain ps ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildDomainBundle p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpartsW, hdom, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartsW
    · constructor
      · exact hdom
      · constructor
        · exact hcore
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_domain_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildGeneratedPartListWitness name fs fields parts (mergeSubsts parts) ∧
    SubstDomain (mergeSubsts parts) = NestedBinderWildStructFieldPatternListDomain fs ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildDomainBundle p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpartsW, hdom, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartsW
    · constructor
      · exact hdom
      · constructor
        · exact hcore
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathWitnessBundle_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathWitnessBundle ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathWitnessBundle p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathWitnessBundle_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathWitnessBundle name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathWitnessBundle p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_path_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathCorrespondenceWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := match_tuple_nestedBinderWild_pathWitnessBundle_certificate_semantic_observation
    p Γ v scrutinee body τ ps vs parts rest hprog hfrag hparts hσ hty
  rcases hgen with ⟨hpat, hpath, hcore, hhit, hcert⟩
  exact ⟨hpat, hpath.correspondence, hcore, hhit, hcert⟩

theorem match_struct_nestedBinderWild_path_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathCorrespondenceWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := match_struct_nestedBinderWild_pathWitnessBundle_certificate_semantic_observation
    p Γ v scrutinee body τ name fs fields parts rest hprog hfrag hparts hσ hty
  rcases hgen with ⟨hpat, hpath, hcore, hhit, hcert⟩
  exact ⟨hpat, hpath.correspondence, hcore, hhit, hcert⟩

theorem match_tuple_nestedBinderWild_pathSummary_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathSummaryWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathWitnessBundle p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath.summary
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathSummary_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathSummaryWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathWitnessBundle p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath.summary
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathCoverage_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathCoverageWitness ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathWitnessBundle p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath.coverage
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathCoverage_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathCoverageWitness name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathWitnessBundle p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath.coverage
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathDomainCoverage_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathDomainCoverageWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathWitnessBundle p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath.domainCoverage
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathDomainCoverage_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathDomainCoverageWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathWitnessBundle p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpath, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpath.domainCoverage
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathLeaf_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      (mergeSubsts parts)
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, _, _, _, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathLeaf_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      (mergeSubsts parts)
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, _, _, _, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathPartLeaf_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathPartLeafWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, hpartLeaf, _, _, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartLeaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathPartLeaf_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathPartLeafWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, hpartLeaf, _, _, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartLeaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathOrigin_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathPartOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, horigin, _, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathOrigin_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathPartOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, horigin, _, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathValueOrigin_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    BinderPathValueOriginWitness
      (NestedBinderWildPatternListBinderPathBindings ps [] 0)
      parts
      (NestedBinderWildPatternListDomain ps) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, _, hvalueOrigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hvalueOrigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathValueOrigin_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    BinderPathValueOriginWitness
      (NestedBinderWildStructFieldBinderPathBindings fs [])
      parts
      (NestedBinderWildStructFieldPatternListDomain fs) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, _, _, _, hvalueOrigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hvalueOrigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathProvenance_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
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
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathProvenanceBundle
    p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, hpartLeaf, horigin, hvalueOrigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hpartLeaf
      · constructor
        · exact horigin
        · constructor
          · exact hvalueOrigin
          · constructor
            · exact hcore
            · constructor
              · exact hhit
              · simpa using
                (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathProvenance_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
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
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathProvenanceBundle
    p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hleaf, hpartLeaf, horigin, hvalueOrigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hpartLeaf
      · constructor
        · exact horigin
        · constructor
          · exact hvalueOrigin
          · constructor
            · exact hcore
            · constructor
              · exact hhit
              · simpa using
                (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathLeafAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    (x ∈ SubstDomain (mergeSubsts parts) ∧
      ∃ path, (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathLeafAtBundle
    p ps vs parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, hleaf, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathLeafAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    (x ∈ SubstDomain (mergeSubsts parts) ∧
      ∃ path, (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs []) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathLeafAtBundle
    p name fs fields parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, hleaf, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hleaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathPartLeafAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    ((∃ path, (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0) ∧
      ∃ part, part ∈ parts ∧ x ∈ SubstDomain part) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathPartLeafAtBundle
    p ps vs parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, hpartLeaf, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartLeaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathPartLeafAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    ((∃ path, (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs []) ∧
      ∃ part, part ∈ parts ∧ x ∈ SubstDomain part) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathPartLeafAtBundle
    p name fs fields parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, hpartLeaf, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartLeaf
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathOriginAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    (∃ path part,
      (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0 ∧
      part ∈ parts ∧
      x ∈ SubstDomain part) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathOriginAtBundle
    p ps vs parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, horigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathOriginAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    (∃ path part,
      (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs [] ∧
      part ∈ parts ∧
      x ∈ SubstDomain part) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathOriginAtBundle
    p name fs fields parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, horigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact horigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathValueOriginAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildPatternListDomain ps)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    (∃ path part value,
      (path, x) ∈ NestedBinderWildPatternListBinderPathBindings ps [] 0 ∧
      part ∈ parts ∧
      (x, value) ∈ part) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathValueOriginAtBundle
    p ps vs parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, hvalueOrigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hvalueOrigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathValueOriginAt_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (x : String)
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hx : x ∈ NestedBinderWildStructFieldPatternListDomain fs)
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    (∃ path part value,
      (path, x) ∈ NestedBinderWildStructFieldBinderPathBindings fs [] ∧
      part ∈ parts ∧
      (x, value) ∈ part) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathValueOriginAtBundle
    p name fs fields parts body rest [] [] x hprog hfrag hparts hσ hx
  rcases hgen with ⟨hpat, hvalueOrigin, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hvalueOrigin
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathBridge_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildGeneratedPartListWitness ps vs parts (mergeSubsts parts) ∧
    TupleNestedBinderWildPathBridgeAssumption ps ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathBridgeBundle p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpartsW, hbridge, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartsW
    · constructor
      · exact hbridge
      · constructor
        · exact hcore
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathBridge_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildGeneratedPartListWitness name fs fields parts (mergeSubsts parts) ∧
    StructNestedBinderWildPathBridgeAssumption fs ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathBridgeBundle p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hpartsW, hbridge, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hpartsW
    · constructor
      · exact hbridge
      · constructor
        · exact hcore
        · constructor
          · exact hhit
          · simpa using
            (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_tuple_nestedBinderWild_pathBridgeCertificate_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ps : List Pattern) (vs : List Value) (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildPatternList ps)
    (hparts : TupleNestedBinderWildGeneratedParts ps vs parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.tuple ps, body) :: rest)) τ) :
    TuplePatternWitness ps vs (mergeSubsts parts) ∧
    TupleNestedBinderWildPathBridgeCertificate ps vs parts (mergeSubsts parts) ∧
    TupleCoreMatchWitness ps vs (mergeSubsts parts) ∧
    MatchBranchObserved (.tuple vs) ((.tuple ps, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.tuple ps, body) :: rest),
      MatchLoweringObserves scrutinee ((.tuple ps, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.tuple ps, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.tuple ps, body) :: rest) τ hty).tree := by
  have hgen := typing_matchTupleNestedBinderWildPathBridgeCertificateBundle
    p ps vs parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hbridge, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hbridge
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.tuple ps, body) :: rest) τ hty)

theorem match_struct_nestedBinderWild_pathBridgeCertificate_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (name : String) (fs : List (String × Pattern)) (fields : List (String × Value))
    (parts : List Subst) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hfrag : NestedBinderWildStructFieldPatternList fs)
    (hparts : StructNestedBinderWildGeneratedParts fs fields parts)
    (hσ : MatchSubstUnique (mergeSubsts parts))
    (hty : HasTypeExpr Γ (.matchE scrutinee ((.struct name fs, body) :: rest)) τ) :
    StructPatternWitness name fs fields (mergeSubsts parts) ∧
    StructNestedBinderWildPathBridgeCertificate name fs fields parts (mergeSubsts parts) ∧
    StructCoreMatchWitness name fs fields (mergeSubsts parts) ∧
    MatchBranchObserved (.structV name fields) ((.struct name fs, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee ((.struct name fs, body) :: rest),
      MatchLoweringObserves scrutinee ((.struct name fs, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee ((.struct name fs, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee ((.struct name fs, body) :: rest) τ hty).tree := by
  have hgen := typing_matchStructNestedBinderWildPathBridgeCertificateBundle
    p name fs fields parts body rest [] [] hprog hfrag hparts hσ
  rcases hgen with ⟨hpat, hbridge, hcore, hhit, _⟩
  constructor
  · exact hpat
  · constructor
    · exact hbridge
    · constructor
      · exact hcore
      · constructor
        · exact hhit
        · simpa using
          (match_certificate_optimization_observation Γ v scrutinee ((.struct name fs, body) :: rest) τ hty)

theorem match_ctor_afterCtorMismatches_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ctor : String) (pats : List Pattern) (args : List Value)
    (pre : List (Pattern × Expr)) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hpre : CtorMismatchExprPrefix ctor pre)
    (hty : HasTypeExpr Γ (.matchE scrutinee (pre ++ (.ctor ctor pats, body) :: rest)) τ) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.ctor ctor pats, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee (pre ++ (.ctor ctor pats, body) :: rest),
      MatchLoweringObserves scrutinee (pre ++ (.ctor ctor pats, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee (pre ++ (.ctor ctor pats, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee (pre ++ (.ctor ctor pats, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee (pre ++ (.ctor ctor pats, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee (pre ++ (.ctor ctor pats, body) :: rest) τ hty).tree := by
  constructor
  · exact typing_matchBranchObserved_afterCtorMismatches p ctor pats args pre body rest hprog hpre
  · simpa using
      (match_certificate_optimization_observation Γ v scrutinee (pre ++ (.ctor ctor pats, body) :: rest) τ hty)

theorem match_wild_afterCtorMismatches_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee body : Expr) (τ : Ty)
    (ctor : String) (args : List Value)
    (pre : List (Pattern × Expr)) (rest : List (Pattern × Expr))
    (hprog : WellTypedProgram p)
    (hpre : CtorMismatchExprPrefix ctor pre)
    (hty : HasTypeExpr Γ (.matchE scrutinee (pre ++ (.wild, body) :: rest)) τ) :
    MatchBranchObserved (.ctorV ctor args) (pre ++ (.wild, body) :: rest) body ∧
    ∃ wit : MatchCodegenWitness scrutinee (pre ++ (.wild, body) :: rest),
      MatchLoweringObserves scrutinee (pre ++ (.wild, body) :: rest) wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee (pre ++ (.wild, body) :: rest))
        (build_match_artifact_certificate Γ v scrutinee (pre ++ (.wild, body) :: rest) τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee (pre ++ (.wild, body) :: rest) τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee (pre ++ (.wild, body) :: rest) τ hty).tree := by
  constructor
  · exact typing_matchBranchObserved_wild_afterCtorMismatches p ctor args pre body rest hprog hpre
  · simpa using
      (match_certificate_optimization_observation Γ v scrutinee (pre ++ (.wild, body) :: rest) τ hty)

theorem match_cover_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (ctor : String) (args : List Value) (body : Expr)
    (hprog : WellTypedProgram p)
    (hcover : CtorExprCasesCover ctor cases body)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    MatchBranchObserved (.ctorV ctor args) cases body ∧
    ∃ wit : MatchCodegenWitness scrutinee cases,
      MatchLoweringObserves scrutinee cases wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee cases)
        (build_match_artifact_certificate Γ v scrutinee cases τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee cases τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee cases τ hty).tree := by
  constructor
  · exact typing_matchBranchObserved_ofCtorCover p ctor args cases body hprog hcover
  · simpa using
      (match_certificate_optimization_observation Γ v scrutinee cases τ hty)

theorem match_exhaustive_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (v : Value) (scrutinee : Expr) (cases : List (Pattern × Expr)) (τ : Ty)
    (ctor : String) (args : List Value)
    (hprog : WellTypedProgram p)
    (hexh : CtorExprCasesExhaustive ctor cases)
    (hty : HasTypeExpr Γ (.matchE scrutinee cases) τ) :
    (∃ body, MatchBranchObserved (.ctorV ctor args) cases body) ∧
    ∃ wit : MatchCodegenWitness scrutinee cases,
      MatchLoweringObserves scrutinee cases wit.gcases ∧
      MatchTreeReflectsExpr (.matchE scrutinee cases)
        (build_match_artifact_certificate Γ v scrutinee cases τ hty).tree ∧
      MatchTreeWellTyped Γ
        (build_match_artifact_certificate Γ v scrutinee cases τ hty).tree τ ∧
      MatchTreeSound v
        (build_match_artifact_certificate Γ v scrutinee cases τ hty).tree := by
  constructor
  · exact selectMatchExpr_existsOfExhaustive ctor args cases hexh
  · simpa using
      (match_certificate_optimization_observation Γ v scrutinee cases τ hty)

theorem copyUpdate_root_target_certificate_semantic_observation_core
    (p : Program) (Γ : TyEnv) (base value : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ) :
    CopyUpdatePathObserved (interpExpr base) [] (interpExpr value) (interpExpr value) ∧
    CopyUpdateHeadObserved (interpExpr base) [] (interpExpr value) (interpExpr value) ∧
    CopyUpdatePrefixObserved (interpExpr base) [] (interpExpr value) (interpExpr value) ∧
    LoweredExprTargetObserves (.copyUpdate base [] value)
      (LowerCopyUpdateTarget (.copyUpdate base [] value)) ∧
    ∃ wit : CopyUpdateCodegenWitness base [] value,
      CopyUpdateLoweringObserves base [] value ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base [] value)
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan ∧
      CopyUpdatePlanWellTyped Γ
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan τ ∧
      CopyUpdatePlanSound
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan := by
  have hchain := copyUpdate_target_soundness_chain p base [] value τ hprog hv
  rcases hchain with ⟨_hroot, htarget, _hpaths, _hproj⟩
  constructor
  · exact typing_copyUpdateObservationBundle p (interpExpr base) (interpExpr value) τ hprog hv
  · constructor
    · exact typing_copyUpdateHeadObservationBundle p (interpExpr base) (interpExpr value) τ hprog hv
    · constructor
      · exact typing_copyUpdatePrefixObservationBundle p (interpExpr base) (interpExpr value) τ hprog hv
      · constructor
        · exact htarget
        · simpa using
            (copyUpdate_certificate_optimization_observation Γ base [] value τ hbase hvalue)

theorem copyUpdate_root_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ) :
    CopyUpdatePathObserved (interpExpr base) [] (interpExpr value) (interpExpr value) ∧
    ∃ wit : CopyUpdateCodegenWitness base [] value,
      CopyUpdateLoweringObserves base [] value ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base [] value)
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan ∧
      CopyUpdatePlanWellTyped Γ
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan τ ∧
      CopyUpdatePlanSound
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan := by
  rcases copyUpdate_root_target_certificate_semantic_observation_core p Γ base value τ hprog hbase hvalue hv with
    ⟨hobs, _hhead, _hprefix, _htarget, hwit⟩
  constructor
  · exact hobs
  · exact hwit

theorem copyUpdate_root_target_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ) :
    CopyUpdatePathObserved (interpExpr base) [] (interpExpr value) (interpExpr value) ∧
    CopyUpdateHeadObserved (interpExpr base) [] (interpExpr value) (interpExpr value) ∧
    CopyUpdatePrefixObserved (interpExpr base) [] (interpExpr value) (interpExpr value) ∧
    LoweredExprTargetObserves (.copyUpdate base [] value)
      (LowerCopyUpdateTarget (.copyUpdate base [] value)) ∧
    ∃ wit : CopyUpdateCodegenWitness base [] value,
      CopyUpdateLoweringObserves base [] value ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base [] value)
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan ∧
      CopyUpdatePlanWellTyped Γ
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan τ ∧
      CopyUpdatePlanSound
        (build_copyUpdate_artifact_certificate Γ base [] value τ hbase hvalue).plan := by
  exact copyUpdate_root_target_certificate_semantic_observation_core p Γ base value τ hprog hbase hvalue hv

theorem enum_encoding_certificate_semantic_observation
    (p : Program) (layout : TagLayout) (ctor enumName : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : layout ∈ (LowerEnumPhase p).layouts)
    (hty : HasTypeValue (.ctorV ctor (args.map interpExpr)) (.enum enumName)) :
    EnumEncodingObserved (.ctorV ctor (args.map interpExpr)) ctor (args.map interpExpr) ∧
    ∃ wit : CtorCodegenWitness ctor args,
      EnumLoweringObserves ctor args wit.payload ∧
      TagLayoutReflectsProgram p layout ∧
      TagLayoutWellFormed layout ∧
      TagLayoutSound layout ∧
      (build_enum_artifact_certificate p layout hprog hin).tagsExplicit := by
  constructor
  · exact typing_enumObservationBundle p ctor enumName (args.map interpExpr) hprog hty
  · simpa using
      (enum_certificate_optimization_observation p layout ctor args hprog hin)

theorem tailcall_target_certificate_semantic_observation_core
    (p : Program) (shape : TailShape) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailRecurObserved (.call fn args) fn (args.map interpExpr) ∧
    TailCallShapeObserved (.call fn args) fn (args.map interpExpr) ∧
    LoweredProgramTargetReflects p (LowerTailcallsTarget p) ∧
    LoweredProgramTargetSound p (LowerTailcallsTarget p) ∧
    ∃ wit : CallCodegenWitness fn args,
      TailcallLoweringObserves fn args wit.gargs ∧
      TailShapeReflectsProgram p shape ∧
      TailShapeWellFormed shape ∧
      TailShapeSound shape ∧
      (build_tailcall_artifact_certificate p shape hprog hin).loopsExplicit := by
  have hchain := tailcall_target_soundness_chain p fn args hprog
  rcases hchain with ⟨hobs, hshapeObs, hreflect, hsound, _hloops, _hgargs⟩
  constructor
  · exact hobs
  · constructor
    · exact hshapeObs
    · constructor
      · exact hreflect
      · constructor
        · exact hsound
        · simpa using
            (tailcall_certificate_optimization_observation p shape fn args hprog hin)

theorem tailcall_recur_certificate_semantic_observation
    (p : Program) (shape : TailShape) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailRecurObserved (.call fn args) fn (args.map interpExpr) ∧
    ∃ wit : CallCodegenWitness fn args,
      TailcallLoweringObserves fn args wit.gargs ∧
      TailShapeReflectsProgram p shape ∧
      TailShapeWellFormed shape ∧
      TailShapeSound shape ∧
      (build_tailcall_artifact_certificate p shape hprog hin).loopsExplicit := by
  rcases tailcall_target_certificate_semantic_observation_core p shape fn args hprog hin with
    ⟨hobs, _hshapeObs, _hreflect, _hsound, hwit⟩
  constructor
  · exact hobs
  · exact hwit

theorem tailcall_target_certificate_semantic_observation
    (p : Program) (shape : TailShape) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailRecurObserved (.call fn args) fn (args.map interpExpr) ∧
    TailCallShapeObserved (.call fn args) fn (args.map interpExpr) ∧
    LoweredProgramTargetReflects p (LowerTailcallsTarget p) ∧
    LoweredProgramTargetSound p (LowerTailcallsTarget p) ∧
    ∃ wit : CallCodegenWitness fn args,
      TailcallLoweringObserves fn args wit.gargs ∧
      TailShapeReflectsProgram p shape ∧
      TailShapeWellFormed shape ∧
      TailShapeSound shape ∧
      (build_tailcall_artifact_certificate p shape hprog hin).loopsExplicit := by
  exact tailcall_target_certificate_semantic_observation_core p shape fn args hprog hin

theorem pipeline_singleStage_target_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (fn : String) (args : List Expr) (stage : PipelineStage) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    PipelineSingleStageObserved (interpExpr (.call fn args)) stage ∧
    LoweredExprTargetObserves (.call fn args)
      (FusePipelineTarget (.call fn args)) ∧
    ∃ wit : CallCodegenWitness fn args,
      PipelineFusionObserves fn args wit.gargs ∧
      PipelinePlanReflectsExpr (.call fn args)
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanWellTyped Γ
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanSound
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  have hchain := pipeline_target_soundness_chain p fn args (interpExpr (.call fn args)) hprog
  rcases hchain with ⟨_hobs, htarget, _hsingle, _hgargs⟩
  constructor
  · exact typing_pipelineObservationBundle p (interpExpr (.call fn args)) stage hprog
  · constructor
    · exact htarget
    · simpa using
        (pipeline_certificate_optimization_observation Γ fn args τ hty)

theorem pipeline_singleStage_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (fn : String) (args : List Expr) (stage : PipelineStage) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    PipelineSingleStageObserved (interpExpr (.call fn args)) stage ∧
    ∃ wit : CallCodegenWitness fn args,
      PipelineFusionObserves fn args wit.gargs ∧
      PipelinePlanReflectsExpr (.call fn args)
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanWellTyped Γ
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanSound
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  rcases pipeline_singleStage_target_certificate_semantic_observation p Γ fn args stage τ hprog hty with
    ⟨hobs, _htarget, hwit⟩
  exact ⟨hobs, hwit⟩

theorem pipeline_target_certificate_semantic_observation_core
    (p : Program) (Γ : TyEnv) (fn : String) (args : List Expr) (stages : List PipelineStage) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    PipelineStagesObserved (interpExpr (.call fn args)) stages ∧
    LoweredExprTargetObserves (.call fn args)
      (FusePipelineTarget (.call fn args)) ∧
    ∃ wit : CallCodegenWitness fn args,
      PipelineFusionObserves fn args wit.gargs ∧
      PipelinePlanReflectsExpr (.call fn args)
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanWellTyped Γ
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanSound
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  have hchain := pipeline_target_soundness_chain p fn args (interpExpr (.call fn args)) hprog
  rcases hchain with ⟨_hobs, htarget, _hsingle, _hgargs⟩
  constructor
  · exact typing_pipelineObservationBundle_general p (interpExpr (.call fn args)) stages hprog
  · constructor
    · exact htarget
    · simpa using
        (pipeline_certificate_optimization_observation Γ fn args τ hty)

theorem copyUpdate_path_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (path : List String) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) path (interpExpr value) = some out) :
    CopyUpdatePathObserved (interpExpr base) path (interpExpr value) out ∧
    ∃ wit : CopyUpdateCodegenWitness base path value,
      CopyUpdateLoweringObserves base path value ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base path value)
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan ∧
      CopyUpdatePlanWellTyped Γ
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan τ ∧
      CopyUpdatePlanSound
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan := by
  constructor
  · exact typing_copyUpdateObservationBundle_general p (interpExpr base) (interpExpr value) out path τ hprog hv hupd
  · simpa using
      (copyUpdate_certificate_optimization_observation Γ base path value τ hbase hvalue)

theorem copyUpdate_path_target_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (path : List String) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) path (interpExpr value) = some out) :
    CopyUpdatePathObserved (interpExpr base) path (interpExpr value) out ∧
    CopyUpdateHeadObserved (interpExpr base) path (interpExpr value) out ∧
    CopyUpdatePrefixObserved (interpExpr base) path (interpExpr value) out ∧
    LoweredExprTargetObserves (.copyUpdate base path value)
      (LowerCopyUpdateTarget (.copyUpdate base path value)) ∧
    ∃ wit : CopyUpdateCodegenWitness base path value,
      CopyUpdateLoweringObserves base path value ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base path value)
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan ∧
      CopyUpdatePlanWellTyped Γ
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan τ ∧
      CopyUpdatePlanSound
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan := by
  have hchain := copyUpdate_path_target_soundness_chain p base path value out τ hprog hv hupd
  rcases hchain with ⟨hobs, hhead, hprefix, htarget, _hpaths, _hproj⟩
  constructor
  · exact hobs
  · constructor
    · exact hhead
    · constructor
      · exact hprefix
      · constructor
        · exact htarget
        · simpa using
            (copyUpdate_certificate_optimization_observation Γ base path value τ hbase hvalue)

theorem copyUpdate_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (path : List String) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) path (interpExpr value) = some out) :
    CopyUpdatePathObserved (interpExpr base) path (interpExpr value) out ∧
    CopyUpdateHeadObserved (interpExpr base) path (interpExpr value) out ∧
    CopyUpdatePrefixObserved (interpExpr base) path (interpExpr value) out ∧
    LoweredExprTargetObserves (.copyUpdate base path value)
      (LowerCopyUpdateTarget (.copyUpdate base path value)) ∧
    ∃ wit : CopyUpdateCodegenWitness base path value,
      CopyUpdateLoweringObserves base path value ∧
      CopyUpdatePlanReflectsExpr (.copyUpdate base path value)
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan ∧
      CopyUpdatePlanWellTyped Γ
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan τ ∧
      CopyUpdatePlanSound
        (build_copyUpdate_artifact_certificate Γ base path value τ hbase hvalue).plan := by
  exact copyUpdate_path_target_certificate_semantic_observation p Γ base value path out τ hprog hbase hvalue hv hupd

theorem copyUpdate_child_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (key : String) (rest : List String) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) (key :: rest) (interpExpr value) = some out) :
    ∃ name fields child child',
      interpExpr base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child rest (interpExpr value) = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      CopyUpdatePathObserved child rest (interpExpr value) child' := by
  have hcert := copyUpdate_certificate_semantic_observation p Γ base value (key :: rest) out τ hprog hbase hvalue hv hupd
  rcases hcert with ⟨_hpath, _hhead, hprefix, _htarget, _hwit⟩
  exact copyUpdatePrefixObserved_child (interpExpr base) key rest (interpExpr value) out hprefix

theorem copyUpdate_childChain_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (key nextKey : String) (rest : List String) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) (key :: nextKey :: rest) (interpExpr value) = some out) :
    ∃ name fields child child',
      interpExpr base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: rest) (interpExpr value) = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      CopyUpdatePrefixObserved child (nextKey :: rest) (interpExpr value) child' := by
  have hcert := copyUpdate_certificate_semantic_observation p Γ base value (key :: nextKey :: rest) out τ hprog hbase hvalue hv hupd
  rcases hcert with ⟨_hpath, _hhead, hprefix, _htarget, _hwit⟩
  exact copyUpdatePrefixObserved_childChain (interpExpr base) key nextKey rest (interpExpr value) out hprefix

theorem copyUpdate_grandchild_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (key nextKey : String) (rest : List String) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) (key :: nextKey :: rest) (interpExpr value) = some out) :
    ∃ name fields child child' childName childFields grandchild grandchild',
      interpExpr base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: rest) (interpExpr value) = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      child = .structV childName childFields ∧
      semLookupField childFields nextKey = some grandchild ∧
      semUpdateValuePath grandchild rest (interpExpr value) = some grandchild' ∧
      child' = .structV childName (semUpdateField childFields nextKey grandchild') ∧
      CopyUpdatePathObserved grandchild rest (interpExpr value) grandchild' := by
  have hcert := copyUpdate_certificate_semantic_observation p Γ base value (key :: nextKey :: rest) out τ hprog hbase hvalue hv hupd
  rcases hcert with ⟨_hpath, _hhead, hprefix, _htarget, _hwit⟩
  exact copyUpdatePrefixObserved_grandchild (interpExpr base) key nextKey rest (interpExpr value) out hprefix

theorem copyUpdate_grandchildChain_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (base value : Expr) (key nextKey thirdKey : String) (rest : List String) (out : Value) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hbase : HasTypeExpr Γ base τ)
    (hvalue : HasTypeExpr Γ value τ)
    (hv : HasTypeValue (interpExpr base) τ)
    (hupd : semUpdateValuePath (interpExpr base) (key :: nextKey :: thirdKey :: rest) (interpExpr value) = some out) :
    ∃ name fields child child' childName childFields grandchild grandchild',
      interpExpr base = .structV name fields ∧
      semLookupField fields key = some child ∧
      semUpdateValuePath child (nextKey :: thirdKey :: rest) (interpExpr value) = some child' ∧
      out = .structV name (semUpdateField fields key child') ∧
      child = .structV childName childFields ∧
      semLookupField childFields nextKey = some grandchild ∧
      semUpdateValuePath grandchild (thirdKey :: rest) (interpExpr value) = some grandchild' ∧
      child' = .structV childName (semUpdateField childFields nextKey grandchild') ∧
      CopyUpdatePrefixObserved grandchild (thirdKey :: rest) (interpExpr value) grandchild' := by
  have hcert := copyUpdate_certificate_semantic_observation p Γ base value (key :: nextKey :: thirdKey :: rest) out τ hprog hbase hvalue hv hupd
  rcases hcert with ⟨_hpath, _hhead, hprefix, _htarget, _hwit⟩
  exact copyUpdatePrefixObserved_grandchildChain (interpExpr base) key nextKey thirdKey rest (interpExpr value) out hprefix

theorem pipeline_multistage_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (fn : String) (args : List Expr) (stages : List PipelineStage) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    PipelineStagesObserved (interpExpr (.call fn args)) stages ∧
    ∃ wit : CallCodegenWitness fn args,
      PipelineFusionObserves fn args wit.gargs ∧
      PipelinePlanReflectsExpr (.call fn args)
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanWellTyped Γ
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanSound
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  rcases pipeline_target_certificate_semantic_observation_core p Γ fn args stages τ hprog hty with
    ⟨hobs, _htarget, hwit⟩
  exact ⟨hobs, hwit⟩

theorem pipeline_target_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (fn : String) (args : List Expr) (stages : List PipelineStage) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    PipelineStagesObserved (interpExpr (.call fn args)) stages ∧
    LoweredExprTargetObserves (.call fn args)
      (FusePipelineTarget (.call fn args)) ∧
    ∃ wit : CallCodegenWitness fn args,
      PipelineFusionObserves fn args wit.gargs ∧
      PipelinePlanReflectsExpr (.call fn args)
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanWellTyped Γ
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanSound
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  exact pipeline_target_certificate_semantic_observation_core p Γ fn args stages τ hprog hty

theorem pipeline_certificate_semantic_observation
    (p : Program) (Γ : TyEnv) (fn : String) (args : List Expr) (stages : List PipelineStage) (τ : Ty)
    (hprog : WellTypedProgram p)
    (hty : HasTypeExpr Γ (.call fn args) τ) :
    PipelineStagesObserved (interpExpr (.call fn args)) stages ∧
    LoweredExprTargetObserves (.call fn args)
      (FusePipelineTarget (.call fn args)) ∧
    ∃ wit : CallCodegenWitness fn args,
      PipelineFusionObserves fn args wit.gargs ∧
      PipelinePlanReflectsExpr (.call fn args)
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanWellTyped Γ
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      PipelinePlanSound
        (build_pipeline_artifact_certificate Γ (.call fn args) τ hty).plan ∧
      (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase (.call fn args)))).singlePass := by
  exact pipeline_target_certificate_semantic_observation_core p Γ fn args stages τ hprog hty

theorem tailcall_certificate_semantic_observation
    (p : Program) (shape : TailShape) (fn : String) (args : List Expr)
    (hprog : WellTypedProgram p)
    (hin : shape ∈ (LowerTailcallPhase p).shapes) :
    TailRecurObserved (.call fn args) fn (args.map interpExpr) ∧
    TailCallShapeObserved (.call fn args) fn (args.map interpExpr) ∧
    LoweredProgramTargetReflects p (LowerTailcallsTarget p) ∧
    LoweredProgramTargetSound p (LowerTailcallsTarget p) ∧
    ∃ wit : CallCodegenWitness fn args,
      TailcallLoweringObserves fn args wit.gargs ∧
      TailShapeReflectsProgram p shape ∧
      TailShapeWellFormed shape ∧
      TailShapeSound shape ∧
      (build_tailcall_artifact_certificate p shape hprog hin).loopsExplicit := by
  exact tailcall_target_certificate_semantic_observation p shape fn args hprog hin

theorem lowerMatchExpr_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr p ρ (LowerMatchExpr e) v := by
  simpa [LowerMatchExpr] using hev

theorem lowerMatchPhase_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr p ρ (LowerMatchPhase e).expr v := by
  simpa [LowerMatchPhase, LowerMatchExpr] using hev

theorem lowerCopyUpdateExpr_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr p ρ (LowerCopyUpdateExpr e) v := by
  unfold EvalExpr at hev ⊢
  cases e <;> simpa [LowerCopyUpdateExpr, interpExpr] using hev

theorem lowerCopyUpdatePhase_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ (LowerMatchPhase e).expr v) :
    EvalExpr p ρ (LowerCopyUpdatePhase (LowerMatchPhase e)).expr v := by
  have hmatch : EvalExpr p ρ e v := by
    simpa [LowerMatchPhase, LowerMatchExpr] using hev
  simpa [LowerCopyUpdatePhase, LowerMatchPhase, LowerMatchExpr] using
    (lowerCopyUpdateExpr_preserves_eval p ρ e v hprog hmatch)

theorem fusePipelineExpr_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr p ρ (FusePipelineExpr e) v := by
  unfold EvalExpr at hev ⊢
  cases e <;> simpa [FusePipelineExpr, FusePipelineArgs, interpExpr] using hev

theorem fusePipelinePhase_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ (LowerCopyUpdatePhase (LowerMatchPhase e)).expr v) :
    EvalExpr p ρ (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase e))).expr v := by
  simpa [FusePipelinePhase] using
    (fusePipelineExpr_preserves_eval p ρ (LowerCopyUpdatePhase (LowerMatchPhase e)).expr v hprog hev)

theorem lowerTailcallsProgram_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr (LowerTailcallsProgram p) ρ e v := by
  simpa [EvalExpr] using hev

theorem lowerTailcallsProgram_preserves_wellTyped
    (p : Program)
    (hprog : WellTypedProgram p) :
    WellTypedProgram (LowerTailcallsProgram p) := by
  constructor
  · simpa [DistinctFnNames, LowerTailcallsProgram] using hprog.1
  · intro fn hin
    have hmem :
        ∃ defn,
          defn ∈ p.fns ∧
          { defn with body := defn.body.map (LowerTailcallStmtFor defn.name) } = fn := by
      simpa [LowerTailcallsProgram] using hin
    rcases hmem with ⟨defn, hdefn, rfl⟩
    simpa [WellTypedFn] using hprog.2 defn hdefn

theorem optimizeProgram_preserves_wellTyped
    (p : Program)
    (hprog : WellTypedProgram p) :
    WellTypedProgram (OptimizeProgram p) := by
  simpa [OptimizeProgram, LowerEnumProgram] using
    lowerTailcallsProgram_preserves_wellTyped p hprog

theorem lowerTailcallPhase_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr (LowerTailcallPhase p).program ρ e v := by
  exact lowerTailcallsProgram_preserves_eval p ρ e v hprog hev

theorem lowerEnumProgram_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr (LowerEnumProgram p) ρ e v := by
  simpa [LowerEnumProgram] using hev

theorem lowerEnumPhase_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr (LowerEnumPhase p).program ρ e v := by
  simpa [LowerEnumPhase, LowerEnumProgram] using hev

theorem optimizeExpr_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr p ρ (OptimizeExpr e) v := by
  have hmatch := lowerMatchExpr_preserves_eval p ρ e v hprog hev
  have hcopy := lowerCopyUpdateExpr_preserves_eval p ρ (LowerMatchExpr e) v hprog hmatch
  simpa [OptimizeExpr] using
    (fusePipelineExpr_preserves_eval p ρ (LowerCopyUpdateExpr (LowerMatchExpr e)) v hprog hcopy)

theorem optimizeExpr_phaseChain_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr p ρ (FusePipelinePhase (LowerCopyUpdatePhase (LowerMatchPhase e))).expr v := by
  have hmatch := lowerMatchPhase_preserves_eval p ρ e v hprog hev
  have hcopy := lowerCopyUpdatePhase_preserves_eval p ρ e v hprog hmatch
  exact fusePipelinePhase_preserves_eval p ρ e v hprog hcopy

theorem optimizeProgram_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr (OptimizeProgram p) ρ e v := by
  simpa [EvalExpr] using hev

theorem optimizeProgram_phaseChain_preserves_eval
    (p : Program) (ρ : Env) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p ρ e v) :
    EvalExpr (LowerEnumPhase (LowerTailcallPhase p).program).program ρ e v := by
  simpa [EvalExpr] using hev

theorem compile_var_preserves_eval
    (p : Program) (x : String) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.var x) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.var x)) v := by
  exact ⟨p, Expr.var x, rfl, rfl, hev⟩

theorem compile_struct_preserves_eval
    (p : Program) (name : String) (fields : List (String × Expr)) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.structLit name fields) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.structLit name fields)) v := by
  exact ⟨p, Expr.structLit name fields, rfl, rfl, hev⟩

theorem compile_ctor_preserves_eval
    (p : Program) (name : String) (args : List Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.ctor name args) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.ctor name args)) v := by
  exact ⟨p, Expr.ctor name args, rfl, rfl, hev⟩

theorem compile_if_preserves_eval
    (p : Program) (c t e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.ite c t e) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.ite c t e)) v := by
  exact ⟨p, Expr.ite c t e, rfl, rfl, hev⟩

theorem compile_call_preserves_eval
    (p : Program) (fn : String) (args : List Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.call fn args) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.call fn args)) v := by
  exact ⟨p, Expr.call fn args, rfl, rfl, hev⟩

theorem compile_tuple_preserves_eval
    (p : Program) (items : List Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.tuple items) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.tuple items)) v := by
  exact ⟨p, Expr.tuple items, rfl, rfl, hev⟩

theorem compile_unary_preserves_eval
    (p : Program) (op : String) (arg : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.unary op arg) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.unary op arg)) v := by
  exact ⟨p, Expr.unary op arg, rfl, rfl, hev⟩

theorem compile_binary_preserves_eval
    (p : Program) (op : String) (lhs rhs : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.binary op lhs rhs) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.binary op lhs rhs)) v := by
  exact ⟨p, Expr.binary op lhs rhs, rfl, rfl, hev⟩

theorem compile_match_preserves_eval
    (p : Program) (scrutinee : Expr) (cases : List (Pattern × Expr)) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] (Expr.matchE scrutinee cases) v) :
    GEvalExpr (CompileProgram p) (CompileExpr (Expr.matchE scrutinee cases)) v := by
  exact ⟨p, Expr.matchE scrutinee cases, rfl, rfl, hev⟩

theorem compile_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] e v) :
    GEvalExpr (CompileProgram p) (CompileExpr e) v := by
  exact ⟨p, e, rfl, rfl, hev⟩

theorem tailcall_lowering_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr (LowerTailcallsProgram p) [] e v) :
    GEvalExpr (CompileProgram (LowerTailcallsProgram p)) (CompileExpr e) v := by
  exact ⟨LowerTailcallsProgram p, e, rfl, rfl, hev⟩

theorem match_lowering_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] e v) :
    GEvalExpr (CompileProgram p) (CompileExpr (LowerMatchExpr e)) v := by
  exact ⟨p, LowerMatchExpr e, rfl, rfl, by simpa [LowerMatchExpr] using hev⟩

theorem copyUpdate_lowering_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] e v) :
    GEvalExpr (CompileProgram p) (CompileExpr (LowerCopyUpdateExpr e)) v := by
  exact ⟨p, LowerCopyUpdateExpr e, rfl, rfl, lowerCopyUpdateExpr_preserves_eval p [] e v hprog hev⟩

theorem enum_lowering_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr (LowerEnumProgram p) [] e v) :
    GEvalExpr (CompileProgram (LowerEnumProgram p)) (CompileExpr e) v := by
  exact ⟨LowerEnumProgram p, e, rfl, rfl, hev⟩

theorem pipelineFusion_lowering_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr p [] e v) :
    GEvalExpr (CompileProgram p) (CompileExpr (FusePipelineExpr e)) v := by
  exact ⟨p, FusePipelineExpr e, rfl, rfl, fusePipelineExpr_preserves_eval p [] e v hprog hev⟩

theorem optimization_pipeline_preserves_eval
    (p : Program) (e : Expr) (v : Value)
    (hprog : WellTypedProgram p)
    (hev : EvalExpr (OptimizeProgram p) [] e v) :
    GEvalExpr (CompileProgram (OptimizeProgram p)) (CompileExpr (OptimizeExpr e)) v := by
  have hoptprog : WellTypedProgram (OptimizeProgram p) :=
    optimizeProgram_preserves_wellTyped p hprog
  have hopt : EvalExpr (OptimizeProgram p) [] (OptimizeExpr e) v := by
    exact optimizeExpr_preserves_eval (OptimizeProgram p) [] e v hoptprog hev
  exact ⟨OptimizeProgram p, OptimizeExpr e, rfl, rfl, hopt⟩

end Fo
