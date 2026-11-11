module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof InternalQuotientComparisonProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (fuelRename withHyp)
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundCoreProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundProof
open OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem ownFuelTerminated (s t m : Program 2) (required workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode))) :
    Nonempty (Derivation body Gamma (TerminatedWork s t m required workCode)) :=
  sufficientFuel s t m workCode required required hf ⟨equalToNext (refl required)⟩

theorem saturatedForward (s t m : Program 2) (required count workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork s t m count workCode))) :
    Nonempty (Derivation body Gamma (WorkAccepted s t m workCode)) := by
  apply weakGapCases required count _ hb
  intro beta j Delta gap hj he
  rw [workAcceptedRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have hs' := renameInto hs j Delta hj
  rw [successfulWorkRename] at hs'
  obtain ⟨he⟩ := he
  have hsum := workRunCountTransport s t m (numeral 2) (count.relabel j)
    (add (required.relabel j) gap) (workCode.relabel j) ⟨symm he⟩ hs'
  have hown := recoverBeforePadding s t m (required.relabel j) gap (workCode.relabel j)
    (ownFuelTerminated s t m (required.relabel j) (workCode.relabel j) hf') hsum
  exact acceptedIntro s t m (workCode.relabel j) (required.relabel j) hf' hown

theorem saturatedBackward (s t m : Program 2) (required count workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted s t m workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork s t m count workCode)) := by
  apply weakGapCases required count _ hb
  intro beta j Delta gap hj he
  rw [successfulWorkRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have ha' := renameInto ha j Delta hj
  rw [workAcceptedRename] at ha'
  have hown := acceptedAtOwnFuel s t m (required.relabel j) (workCode.relabel j) hf' ha'
  have hsum := successfulPadding s t m (required.relabel j) gap (workCode.relabel j) hown
  exact workRunCountTransport s t m (numeral 2) (add (required.relabel j) gap)
    (count.relabel j) (workCode.relabel j) he hsum

theorem actualOriginalHereditaryInternalFuelSaturation :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalFuelSaturation := by
  intro body s t m alpha workCode required count
  let H := WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required count
  let P := SuccessfulWork s t m count workCode
  let Q := WorkAccepted s t m workCode
  have hh : Nonempty (Derivation body [H] H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := saturatedForward s t m required count workCode
    (withHyp (andLeft hh) P) (withHyp (andRight hh) P)
    (show Nonempty (Derivation body [P,H] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := saturatedBackward s t m required count workCode
    (withHyp (andLeft hh) Q) (withHyp (andRight hh) Q)
    (show Nonempty (Derivation body [Q,H] Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationProof
