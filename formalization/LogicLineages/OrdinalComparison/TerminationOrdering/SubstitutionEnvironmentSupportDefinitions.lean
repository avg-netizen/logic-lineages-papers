module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitutionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupport
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation ConfinedSubstitution

/-- Agreement only at real source types; there is no out-of-universe value definition. -/
def Agreement {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) {Γ Δ : List Ty} (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    {P : World I} (ρ : Environment I Γ P) (η : Environment I Δ P) : Prop :=
  ∀ {τ} (v : Variable Γ τ) (ht : τ ∈ TypedExtraDownsets.types I),
    ρ v=interpret ⟨s v,hs v ht⟩ M P η

end LogicLineages.OrdinalComparison.TerminationOrdering.SubstitutionEnvironmentSupport
