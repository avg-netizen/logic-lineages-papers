module
public import LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenamingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitution
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits OriginalSpineActions ConfinedStructuralInterpretation ComparisonFreeVariables

/-- Only potentially occurring source types require confined syntactic replacements. -/
def RangeConfined {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) {Γ Δ : List Ty}
    (s : MarkedSubstitution Symbol arity Γ Δ) : Prop :=
  ∀ {τ} (v : Variable Γ τ),τ ∈ TypedExtraDownsets.types I → Confined I (s v)

/-- Literal bound-variable preservation and absence of protected free names in free replacements. -/
def ProtectedCompatible {Symbol : Type} {arity : Symbol → Nat} (I : Input Symbol arity) {Γ Δ : List Ty}
    (s : MarkedSubstitution Symbol arity Γ Δ) (sourceMask : Protected Γ) (targetMask : Protected Δ) : Prop :=
  ∀ {τ} (v : Variable Γ τ),τ ∈ TypedExtraDownsets.types I →
    (sourceMask v=true → ∃ w : Variable Δ τ,s v=MarkedTerm.var w ∧ targetMask w=true) ∧
    (sourceMask v=false → Supported (s v) (fun {_} w => targetMask w=false))

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitution
