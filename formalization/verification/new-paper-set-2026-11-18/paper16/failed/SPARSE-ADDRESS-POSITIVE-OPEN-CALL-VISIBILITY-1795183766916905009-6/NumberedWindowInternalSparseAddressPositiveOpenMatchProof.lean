module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenMatchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalEqualityTestCompositionProof (equalitySelf)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseAddressPositive

attribute [local irreducible] programGraph equalityTest

private abbrev inputs (p : Program 1) : Fin 2 → Program 3 := ![atAddress p 0,atAddress p 2]
private abbrev values {α : Type} (l r : OTerm α) : Fin 2 → OTerm α := ![l,r]

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem inputValues (p : Program 1) (xs : Fin 3 → OTerm α) (l r : OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph (atAddress p 0) l xs)))
    (right : Nonempty (Derivation body Γ (programGraph (atAddress p 2) r xs))) :
    ∀ i, Nonempty (Derivation body Γ (programGraph (inputs p i) (values l r i) xs)) := by
  intro i
  exact Fin.cases left (Fin.cases right (fun k => Fin.elim0 k)) i

theorem readSame (p : Program 1) (xs : Fin 3 → OTerm α) (l r : OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph (atAddress p 0) l xs)))
    (right : Nonempty (Derivation body Γ (programGraph (atAddress p 2) r xs)))
    (same : Nonempty (Derivation body Γ (programGraph (sameField p) (suc z) xs))) :
    Nonempty (Derivation body Γ (eqn l r)) := by
  have v := compositionRecover equalityTest (inputs p) (suc z) xs (values l r) same
    (inputValues p xs l r left right)
  exact equalityOfAcceptance l r v

theorem introSame (p : Program 1) (xs : Fin 3 → OTerm α) (value : OTerm α)
    (left : Nonempty (Derivation body Γ (programGraph (atAddress p 0) value xs)))
    (right : Nonempty (Derivation body Γ (programGraph (atAddress p 2) value xs))) :
    Nonempty (Derivation body Γ (programGraph (sameField p) (suc z) xs)) := by
  exact compositionValue equalityTest (inputs p) (suc z) xs (values value value)
    (equalitySelf value) (inputValues p xs value value left right)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenMatchProof
