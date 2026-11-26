module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof InternalQuotientComparisonProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof (fuelRename withHyp)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof
open OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalFuelIterationBoundCoreProof
open OriginalTypedDecoderInternalFuelIterationBoundProof
open OriginalTypedDecoderInternalFuelIterationSaturationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem ownFuelTerminated (H : Program 1) (required workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode))) :
    Nonempty (Derivation body Gamma (TerminatedWork H required workCode)) :=
  sufficientFuel H workCode required required hf ⟨equalToNext (refl required)⟩

theorem saturatedForward (H : Program 1) (required count workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H count workCode))) :
    Nonempty (Derivation body Gamma (WorkAccepted H workCode)) := by
  apply weakGapCases required count _ hb
  intro beta j Delta gap hj he
  rw [workAcceptedRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have hs' := renameInto hs j Delta hj
  rw [successfulWorkRename] at hs'
  obtain ⟨he⟩ := he
  have hsum := workRunCountTransport H (numeral 2) (count.relabel j)
    (add (required.relabel j) gap) (workCode.relabel j) ⟨symm he⟩ hs'
  have hown := recoverBeforePadding H (required.relabel j) gap (workCode.relabel j)
    (ownFuelTerminated H (required.relabel j) (workCode.relabel j) hf') hsum
  exact acceptedIntro H (workCode.relabel j) (required.relabel j) hf' hown

theorem saturatedBackward (H : Program 1) (required count workCode : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H workCode))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H count workCode)) := by
  apply weakGapCases required count _ hb
  intro beta j Delta gap hj he
  rw [successfulWorkRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have ha' := renameInto ha j Delta hj
  rw [workAcceptedRename] at ha'
  have hown := acceptedAtOwnFuel H (required.relabel j) (workCode.relabel j) hf' ha'
  have hsum := successfulPadding H (required.relabel j) gap (workCode.relabel j) hown
  exact workRunCountTransport H (numeral 2) (add (required.relabel j) gap)
    (count.relabel j) (workCode.relabel j) he hsum

theorem actualOriginalTypedInternalFuelSaturation :
    OriginalTypedDecoderInternalFuelTargets.ActualOriginalTypedInternalFuelSaturation := by
  intro body H alpha workCode required count
  let A := WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required count
  let P := SuccessfulWork H count workCode
  let Q := WorkAccepted H workCode
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := saturatedForward H required count workCode
    (withHyp (andLeft hh) P) (withHyp (andRight hh) P)
    (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := saturatedBackward H required count workCode
    (withHyp (andLeft hh) Q) (withHyp (andRight hh) Q)
    (show Nonempty (Derivation body [Q,A] Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelIterationSaturationProof
