module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof InternalQuotientComparisonProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuel (workFuel WorkFuelGraph Terminal)
open OriginalTypedDecoderInternalFuelSupportProof (fuelRename withHyp)
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof
open OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalFuelIterationBoundCoreProof
open OriginalTypedDecoderInternalFuelIterationBoundCoreProof (weakGapCases)
open OriginalUniverseDecoderInternalFuelIterationBoundProof
open OriginalUniverseDecoderInternalFuelIterationSaturationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem ownFuelTerminated (H : Program 1) (M contextWindow : Program 2) (required workCode c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode))) :
    Nonempty (Derivation body Gamma (TerminatedWork H M contextWindow required workCode c)) :=
  sufficientFuel H M contextWindow workCode required required c hf ⟨equalToNext (refl required)⟩

theorem saturatedForward (H : Program 1) (M contextWindow : Program 2) (required count workCode c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count)))
    (hs : Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow count workCode c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M contextWindow workCode c)) := by
  apply weakGapCases required count _ hb
  intro beta j Delta gap hj he
  rw [workAcceptedRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have hs' := renameInto hs j Delta hj
  rw [successfulWorkRename] at hs'
  obtain ⟨he⟩ := he
  have hsum := workRunCountTransport H M contextWindow (numeral 2) (count.relabel j)
    (add (required.relabel j) gap) (workCode.relabel j) (c.relabel j) ⟨symm he⟩ hs'
  have hown := recoverBeforePadding H M contextWindow (required.relabel j) gap (workCode.relabel j) (c.relabel j)
    (ownFuelTerminated H M contextWindow (required.relabel j) (workCode.relabel j) (c.relabel j) hf') hsum
  exact acceptedIntro H M contextWindow (workCode.relabel j) (required.relabel j) (c.relabel j) hf' hown

theorem saturatedBackward (H : Program 1) (M contextWindow : Program 2) (required count workCode c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph required workCode)))
    (hb : Nonempty (Derivation body Gamma (InternalPairingSumBounds.weakBound required count)))
    (ha : Nonempty (Derivation body Gamma (WorkAccepted H M contextWindow workCode c))) :
    Nonempty (Derivation body Gamma (SuccessfulWork H M contextWindow count workCode c)) := by
  apply weakGapCases required count _ hb
  intro beta j Delta gap hj he
  rw [successfulWorkRename]
  have hf' := renameInto hf j Delta hj
  rw [fuelRename] at hf'
  have ha' := renameInto ha j Delta hj
  rw [workAcceptedRename] at ha'
  have hown := acceptedAtOwnFuel H M contextWindow (required.relabel j) (workCode.relabel j) (c.relabel j) hf' ha'
  have hsum := successfulPadding H M contextWindow (required.relabel j) gap (workCode.relabel j) (c.relabel j) hown
  exact workRunCountTransport H M contextWindow (numeral 2) (add (required.relabel j) gap)
    (count.relabel j) (workCode.relabel j) (c.relabel j) he hsum

theorem actualOriginalUniverseInternalFuelSaturation :
    OriginalUniverseDecoderInternalFuelTargets.ActualOriginalUniverseInternalFuelSaturation := by
  intro body H M contextWindow alpha workCode required count c
  let A := WorkFuelGraph required workCode ⊓ InternalPairingSumBounds.weakBound required count
  let P := SuccessfulWork H M contextWindow count workCode c
  let Q := WorkAccepted H M contextWindow workCode c
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := saturatedForward H M contextWindow required count workCode c
    (withHyp (andLeft hh) P) (withHyp (andRight hh) P)
    (show Nonempty (Derivation body [P,A] P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := saturatedBackward H M contextWindow required count workCode c
    (withHyp (andLeft hh) Q) (withHyp (andRight hh) Q)
    (show Nonempty (Derivation body [Q,A] Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelIterationSaturationProof
