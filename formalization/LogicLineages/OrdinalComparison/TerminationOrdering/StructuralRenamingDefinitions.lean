module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenaming
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits TypedValueEnvironment OriginalSpineActions ConfinedStructuralInterpretation

def renameSource {Symbol : Type} {arity : Symbol → Nat} {I : Input Symbol arity}
    {Γ Δ : List Ty} {τ : Ty} (r : Renaming Γ Δ) (q : ConfinedTerm I Γ τ) : ConfinedTerm I Δ τ :=
  ⟨renameTerm q.val r,TypeClosureProof.renameAllowed _ q.val r q.property.1,
    LogicLineages.OrdinalComparison.TerminationOrdering.Proof.renameAllowed _ q.val r q.property.2⟩

def pullMask {Γ Δ : List Ty} (r : Renaming Γ Δ) (mask : Protected Δ) : Protected Γ := fun v => mask (r v)

end LogicLineages.OrdinalComparison.TerminationOrdering.StructuralRenaming
