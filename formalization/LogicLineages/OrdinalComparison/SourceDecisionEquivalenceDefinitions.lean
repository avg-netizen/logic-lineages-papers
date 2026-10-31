module
public import LogicLineages.OrdinalComparison.SourceObserverPlanDefinitions
public import LogicLineages.OrdinalComparison.WWGroundPositiveQuerySplitDefinitions
public import LogicLineages.OrdinalComparison.SourceGroundArithmeticCounterDefinitions
public import LogicLineages.OrdinalComparison.SourceBooleanPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DecisionEquivalence
open GroundEquivalence PrimitiveLowering

/-- Conjunction of finite source plans, with the second plan renamed under
EVERY existential binder of the first. It is retained exactly once. -/
def join {Γ} : ExistentialPlan.Plan Γ → ExistentialPlan.Plan Γ → ExistentialPlan.Plan Γ
  | .done,q => q
  | .equation a b p,q => .equation a b (join p q)
  | .gate g p,q => .gate g (join p q)
  | .existsGround p,q => .existsGround (join p (BinaryPlan.renamePlan (Renaming.weaken Γ .ground) q))

def orderDag (strict : Bool) : BooleanWire.Dag 2 1 :=
  .snoc .nil (if strict then .le 1 0 else .lt 1 0)
def ports {Γ} (a b : Port Γ) : Fin 2 → Port Γ := Fin.cons a (Fin.cons b Fin.elim0)
def orderPlan {Γ} (strict : Bool) (a b : Port Γ) : ExistentialPlan.Plan Γ :=
  BooleanPlan.matrixPlan (orderDag strict) (ports a b) 0

def twoGround {Γ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) :
    ∀ σ ∈ Ty.ground::Ty.ground::Γ, σ=Ty.ground := by
  intro σ hs
  simp only [List.mem_cons] at hs
  rcases hs with h|h|h
  · exact h
  · exact h
  · exact hΓ σ h

def request {Γ τ υ} (a : Input Γ τ) (b : Input Γ υ) : Nat × Nat × Nat :=
  (Γ.length,SyntaxCode.encodeTerm a.term,SyntaxCode.encodeTerm b.term)

/-- ALL nonstructural computation is isolated in this uniform numeric map.
The first coordinate is primitive-recursive closed-positive comparison; the
other coordinates are the certified total source anchor evaluator on the
unchanged original source codes. No oracle is assumed. -/
noncomputable def numericData (p : Nat × Nat × Nat) : Bool × Nat × Nat :=
  (GroundPositiveQuerySplit.positiveFlagCode p,
   AbsoluteObserver.openSourceValue (p.1,p.2.1),
   AbsoluteObserver.openSourceValue (p.1,p.2.2))

/-- Pure finite syntax template. Its flags and finite constants are ordinary
input data, NOT semantic predicates. All source terms/DAGs are original typed
syntax; only the two scalar witness names are new before their probe plans. -/
def template {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) (data : Bool × Nat × Nat) : ExistentialPlan.Plan Γ :=
  if data.1 then
    .existsGround (.existsGround
      (join (ObserverPlan.template (twoGround hΓ)
        (ScopedDAG.renameInput (AbsoluteObserver.shiftTwo Γ) a) (.var (.there .here)) data.2.1)
        (join (ObserverPlan.template (twoGround hΓ)
          (ScopedDAG.renameInput (AbsoluteObserver.shiftTwo Γ) b) (.var .here) data.2.2)
          (orderPlan strict (.var (.there .here)) (.var .here)))))
  else .done
noncomputable def realize {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) : ExistentialPlan.Plan Γ :=
  template hΓ strict a b (numericData (request a b))

noncomputable def Universal {Γ τ υ} (strict : Bool) (a : Input Γ τ) (b : Input Γ υ) : Prop :=
  ∀ ρ : Variable Γ .ground → Nat,
    GroundPositiveQuerySplit.QueryAt strict a.term b.term (ExistentialPlan.inputs ρ)

structure GroundOutput where
  context : List Ty
  left : Input context .ground
  right : Input context .ground
structure ArithmeticOutput where
  context : List Ty
  program : BooleanCompiler.Program context

/-- These three templates contain no noncomputable operation. The actual
reductions below are literally their composition with numericData(request). -/
def strictTemplate {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) (data : Bool × Nat × Nat) : GroundOutput :=
  let q := template hΓ strict a b data
  ⟨(ExistentialPlan.compile q).context,(ExistentialPlan.strictPair q).1,(ExistentialPlan.strictPair q).2⟩
def weakTemplate {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) (data : Bool × Nat × Nat) : GroundOutput :=
  let q := template hΓ strict a b data
  ⟨(ExistentialPlan.compile q).context,(ExistentialPlan.weakPair q).1,(ExistentialPlan.weakPair q).2⟩
def arithmeticTemplate {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) (data : Bool × Nat × Nat) : ArithmeticOutput :=
  let g := strictTemplate hΓ strict a b data
  ⟨g.context,GroundArithmeticCounter.counter true g.left g.right⟩
noncomputable def toStrict {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) : GroundOutput := strictTemplate hΓ strict a b (numericData (request a b))
noncomputable def toWeak {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) : GroundOutput := weakTemplate hΓ strict a b (numericData (request a b))
noncomputable def toArithmetic {Γ τ υ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (strict : Bool)
    (a : Input Γ τ) (b : Input Γ υ) : ArithmeticOutput := arithmeticTemplate hΓ strict a b (numericData (request a b))
end LogicLineages.OrdinalComparison.Source.DecisionEquivalence
