module
public import LogicLineages.OrdinalComparison.SourceAffinePlanDefinitions
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ObserverPlan
open GroundEquivalence PrimitiveLowering

/-- Numeric request uses the unchanged original source code, not an assumed
computable encoding of an already closed source. The accepted evaluator uses
raw one at every original ground name. -/
def request {Γ τ} (t : Input Γ τ) : Nat × Nat := (Γ.length,SyntaxCode.encodeTerm t.term)

/-- Executable symbolic finite plan, with one explicitly supplied finite
anchor. The actual source operands are not replaced by scalar formulae. -/
def template {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : Input Γ τ) (v : Port Γ) (C : Nat) : ExistentialPlan.Plan Γ :=
  .existsGround (.existsGround (.equation
    (AbsoluteProbeDAG.originalInput t) (AbsoluteProbeDAG.closedInput hΓ t)
    (AffinePlan.affinePlan (AbsoluteObserver.factor τ) (AbsoluteObserver.factor τ*C)
      (ExistentialPlan.portRename (AbsoluteObserver.shiftTwo Γ) v) (.var .here) (.var (.there .here)))))

/-- The only non-structural step is the separately certified computable numeric
anchor evaluator. No efficiency claim is made for its enormous finite value. -/
noncomputable def realize {Γ τ} (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : Input Γ τ) (v : Port Γ) : ExistentialPlan.Plan Γ :=
  template hΓ t v (AbsoluteObserver.openSourceValue (request t))
end LogicLineages.OrdinalComparison.Source.ObserverPlan
