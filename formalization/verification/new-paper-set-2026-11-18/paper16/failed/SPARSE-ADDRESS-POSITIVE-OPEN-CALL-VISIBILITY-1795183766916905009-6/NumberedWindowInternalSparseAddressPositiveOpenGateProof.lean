module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenTapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenGateProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseAddressPositive

private abbrev testsType (raw : Program 5) (least : Program 3) :=
  conjunction (sameField rawResult) (callFold raw least)
private abbrev testsCtx (raw : Program 5) (least : Program 3) :=
  conjunction (sameField rawContext) (testsType raw least)
private abbrev testsRight (cv tv : Program 1) (raw : Program 5) (least : Program 3) :=
  conjunction (sideGood cv tv 2) (testsCtx raw least)

abbrev Seen (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (p : Program 3) (xs : Fin 3 → OTerm α) : Prop :=
  Nonempty (Derivation body Γ (programGraph p (suc z) xs))

def GateFacts (body : Positive (Fin 1)) {α : Type} (Γ : List (Formula α))
    (cv tv : Program 1) (raw : Program 5) (least : Program 3) (xs : Fin 3 → OTerm α) : Prop :=
  Seen body Γ (sideGood cv tv 0) xs ∧
    (Seen body Γ (sideGood cv tv 2) xs ∧
      (Seen body Γ (sameField rawContext) xs ∧
        (Seen body Γ (sameField rawResult) xs ∧ Seen body Γ (callFold raw least) xs)))

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem gateRead (cv tv : Program 1) (raw : Program 5) (least : Program 3) (xs : Fin 3 → OTerm α)
    (accepted : Seen body Γ (addressPositive cv tv raw least) xs) :
    GateFacts body Γ cv tv raw least xs := by
  obtain ⟨left⟩ := conjunctionRecover (sideGood cv tv 0) (testsRight cv tv raw least) xs accepted
  obtain ⟨right⟩ := conjunctionRecover (sideGood cv tv 2) (testsCtx raw least) xs
    ⟨Derivation.conjunctionRight left⟩
  obtain ⟨context⟩ := conjunctionRecover (sameField rawContext) (testsType raw least) xs
    ⟨Derivation.conjunctionRight right⟩
  obtain ⟨ty⟩ := conjunctionRecover (sameField rawResult) (callFold raw least) xs
    ⟨Derivation.conjunctionRight context⟩
  exact ⟨⟨Derivation.conjunctionLeft left⟩,⟨Derivation.conjunctionLeft right⟩,
    ⟨Derivation.conjunctionLeft context⟩,⟨Derivation.conjunctionLeft ty⟩,⟨Derivation.conjunctionRight ty⟩⟩

theorem gateIntro (cv tv : Program 1) (raw : Program 5) (least : Program 3) (xs : Fin 3 → OTerm α)
    (known : GateFacts body Γ cv tv raw least xs) : Seen body Γ (addressPositive cv tv raw least) xs := by
  obtain ⟨l,r,c,t,h⟩ := known
  have typ := conjunctionAccept (sameField rawResult) (callFold raw least) xs t h
  have ctx := conjunctionAccept (sameField rawContext) (testsType raw least) xs c typ
  have seen := conjunctionAccept (sideGood cv tv 2) (testsCtx raw least) xs r ctx
  exact conjunctionAccept (sideGood cv tv 0) (testsRight cv tv raw least) xs l seen

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveOpenGateProof
