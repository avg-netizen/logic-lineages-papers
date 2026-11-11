module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceInductionSplitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open InternalOriginalOrderSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalTypedDecoderInternalFuelIterationSyntaxProof OriginalTypedDecoderInternalFuelIterationWorkProof
open OriginalTypedDecoderInternalAcceptanceRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem appendForward (H : Program 1) (front suffix joined : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hj : Nonempty (Derivation body Gamma (WorkAccepted H joined))) :
    Nonempty (Derivation body Gamma (WorkAccepted H front ⊓ WorkAccepted H suffix)) := by
  apply acceptedCases H joined _ hj
  intro beta j Delta count hinc hf hr
  simp only [conjunctionRename,workAcceptedRename]
  have ha' := renameInto ha j Delta hinc
  rw [graph2Rename] at ha'
  have hparts := OriginalTypedDecoderInternalAcceptanceInductionSplitProof.successfulSplit H
    count (front.relabel j) (suffix.relabel j) (joined.relabel j) ha' hr
  exact andIntro (successfulAccepted H count (front.relabel j) (andLeft hparts))
    (successfulAccepted H count (suffix.relabel j) (andRight hparts))

theorem appendBackward (H : Program 1) (front suffix joined : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hf : Nonempty (Derivation body Gamma (WorkAccepted H front)))
    (hs : Nonempty (Derivation body Gamma (WorkAccepted H suffix))) :
    Nonempty (Derivation body Gamma (WorkAccepted H joined)) := by
  apply acceptedCases H front _ hf
  intro beta j Delta first hinc hw hr
  rw [workAcceptedRename]
  have ha' := renameInto ha j Delta hinc
  rw [graph2Rename] at ha'
  have hs' := renameInto hs j Delta hinc
  rw [workAcceptedRename] at hs'
  apply acceptedCases H (suffix.relabel j) _ hs'
  intro beta' k Theta second hinc' hw' hr'
  rw [workAcceptedRename]
  have ha'' := renameInto ha' k Theta hinc'
  rw [graph2Rename] at ha''
  have hr'' := renameInto hr k Theta hinc'
  rw [successfulWorkRename] at hr''
  exact successfulAccepted H (OrdinaryArithmetic.addTerm (first.relabel k) second)
    ((joined.relabel j).relabel k)
    (OriginalTypedDecoderInternalAcceptanceInductionProof.successfulAppend H (first.relabel k) second
      ((front.relabel j).relabel k) ((suffix.relabel j).relabel k) ((joined.relabel j).relabel k)
      ha'' hr'' hr')

theorem appendIff (H : Program 1) (front suffix joined : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix))) :
    Nonempty (Derivation body Gamma
      ((WorkAccepted H joined).iff (WorkAccepted H front ⊓ WorkAccepted H suffix))) := by
  let P := WorkAccepted H joined
  let Q := WorkAccepted H front ⊓ WorkAccepted H suffix
  obtain ⟨hf⟩ := appendForward H front suffix joined (withHyp ha P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hq : Nonempty (Derivation body (Q :: Gamma) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := appendBackward H front suffix joined (withHyp ha Q) (andLeft hq) (andRight hq)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem consIff (H : Program 1) (work request suffix singleton : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (StepCons work request suffix)))
    (hs : Nonempty (Derivation body Gamma (StepCons singleton request z))) :
    Nonempty (Derivation body Gamma
      ((WorkAccepted H work).iff (WorkAccepted H singleton ⊓ WorkAccepted H suffix))) :=
  appendIff H singleton suffix work
    (InternalApplicationValidityStackAppendListProof.consBackward singleton request z suffix suffix work
      hs (InternalApplicationValidityStackAppendListProof.appendZeroValue suffix) hc)

theorem actualOriginalTypedInternalWorkAppend :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalWorkAppend := by
  intro body H alpha front suffix joined
  let A := graph2 InternalApplicationValidityStackAppend.append joined front suffix
  obtain ⟨h⟩ := appendIff (body := body) (Gamma := [A]) H front suffix joined
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalTypedInternalWorkCons :
    OriginalTypedDecoderInternalAcceptanceTargets.ActualOriginalTypedInternalWorkCons := by
  intro body H alpha work request suffix singleton
  let A := StepCons work request suffix ⊓ StepCons singleton request z
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consIff H work request suffix singleton (andLeft hh) (andRight hh)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptanceAppendProof
