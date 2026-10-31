module
public import LogicLineages.OrdinalComparison.SourceObserverPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ObserverPlan.Targets
open GroundEquivalence PrimitiveLowering OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def EffectiveAnchor : Prop := Computable AbsoluteObserver.openSourceValue ∧
  ∀ Γ τ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : Input Γ τ),
    AbsoluteObserver.openSourceValue (request t)=AbsoluteObserver.anchor hΓ t.term ∧
    0<AbsoluteObserver.openSourceValue (request t)

def FormulaExact : Prop := ∀ Γ τ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : Input Γ τ)
    (v : Port Γ) (ρ : Variable Γ .ground → Nat),
  ExistentialPlan.Eval ρ (realize hΓ t v) ↔
    AbsoluteObserver.Formula hΓ t.term (ExistentialPlan.inputs ρ) (v.value (ExistentialPlan.inputs ρ))

/-- Actual arbitrary-output source scalar graph, now in the concrete PP plan
accepted by the literal source compiler. This is a decision-equivalence
supplier, not an assertion of a decision algorithm or a whole equivalence. -/
def ObserverExact : Prop := ∀ Γ τ (hΓ : ∀ σ ∈ Γ, σ=Ty.ground) (t : Input Γ τ)
    (v : Port Γ) (ρ : Variable Γ .ground → Nat),
  ExistentialPlan.Eval ρ (realize hΓ t v) ↔
    ∃ w : OrdinalVector Γ τ.level,
      AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t.term=some w ∧
      denote (valuation (UnitObservation.substitution ρ)) (w 0)=
        ((v.value (ExistentialPlan.inputs ρ)) : Ordinal)
end LogicLineages.OrdinalComparison.Source.ObserverPlan.Targets
