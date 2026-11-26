module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceInductionSplitProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceAppendProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z)
open InternalOriginalOrderSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open OriginalTypedDecoderInternalFuelSupportProof (withHyp)
open OriginalUniverseDecoderInternalFuelIterationSyntaxProof OriginalUniverseDecoderInternalFuelIterationWorkProof
open OriginalUniverseDecoderInternalAcceptanceRunProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem appendForward (H : Program 1) (M W : Program 2) (front suffix joined c : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hj : Nonempty (Derivation body Gamma (WorkAccepted H M W joined c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W front c ⊓ WorkAccepted H M W suffix c)) := by
  apply acceptedCases H M W joined c _ hj
  intro beta j Delta count hinc hf hr
  simp only [conjunctionRename,workAcceptedRename]
  have ha' := renameInto ha j Delta hinc
  rw [graph2Rename] at ha'
  have hparts := OriginalUniverseDecoderInternalAcceptanceInductionSplitProof.successfulSplit H M W
    count (front.relabel j) (suffix.relabel j) (joined.relabel j) (c.relabel j) ha' hr
  exact andIntro (successfulAccepted H M W count (front.relabel j) (c.relabel j) (andLeft hparts))
    (successfulAccepted H M W count (suffix.relabel j) (c.relabel j) (andRight hparts))

theorem appendBackward (H : Program 1) (M W : Program 2) (front suffix joined c : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix)))
    (hf : Nonempty (Derivation body Gamma (WorkAccepted H M W front c)))
    (hs : Nonempty (Derivation body Gamma (WorkAccepted H M W suffix c))) :
    Nonempty (Derivation body Gamma (WorkAccepted H M W joined c)) := by
  apply acceptedCases H M W front c _ hf
  intro beta j Delta first hinc hw hr
  rw [workAcceptedRename]
  have ha' := renameInto ha j Delta hinc
  rw [graph2Rename] at ha'
  have hs' := renameInto hs j Delta hinc
  rw [workAcceptedRename] at hs'
  apply acceptedCases H M W (suffix.relabel j) (c.relabel j) _ hs'
  intro beta' k Theta second hinc' hw' hr'
  rw [workAcceptedRename]
  have ha'' := renameInto ha' k Theta hinc'
  rw [graph2Rename] at ha''
  have hr'' := renameInto hr k Theta hinc'
  rw [successfulWorkRename] at hr''
  exact successfulAccepted H M W (OrdinaryArithmetic.addTerm (first.relabel k) second)
    ((joined.relabel j).relabel k) ((c.relabel j).relabel k)
    (OriginalUniverseDecoderInternalAcceptanceInductionProof.successfulAppend H M W (first.relabel k) second
      ((front.relabel j).relabel k) ((suffix.relabel j).relabel k) ((joined.relabel j).relabel k) ((c.relabel j).relabel k)
      ha'' hr'' hr')

theorem appendIff (H : Program 1) (M W : Program 2) (front suffix joined c : OTerm alpha)
    (ha : Nonempty (Derivation body Gamma
      (graph2 InternalApplicationValidityStackAppend.append joined front suffix))) :
    Nonempty (Derivation body Gamma
      ((WorkAccepted H M W joined c).iff (WorkAccepted H M W front c ⊓ WorkAccepted H M W suffix c))) := by
  let P := WorkAccepted H M W joined c
  let Q := WorkAccepted H M W front c ⊓ WorkAccepted H M W suffix c
  obtain ⟨hf⟩ := appendForward H M W front suffix joined c (withHyp ha P)
    (show Nonempty (Derivation body (P :: Gamma) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have hq : Nonempty (Derivation body (Q :: Gamma) Q) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := appendBackward H M W front suffix joined c (withHyp ha Q) (andLeft hq) (andRight hq)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem consIff (H : Program 1) (M W : Program 2) (work request suffix singleton c : OTerm alpha)
    (hc : Nonempty (Derivation body Gamma (StepCons work request suffix)))
    (hs : Nonempty (Derivation body Gamma (StepCons singleton request z))) :
    Nonempty (Derivation body Gamma
      ((WorkAccepted H M W work c).iff (WorkAccepted H M W singleton c ⊓ WorkAccepted H M W suffix c))) :=
  appendIff H M W singleton suffix work c
    (InternalApplicationValidityStackAppendListProof.consBackward singleton request z suffix suffix work
      hs (InternalApplicationValidityStackAppendListProof.appendZeroValue suffix) hc)

theorem actualOriginalUniverseInternalWorkAppend :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalWorkAppend := by
  intro body H M W alpha front suffix joined c
  let A := graph2 InternalApplicationValidityStackAppend.append joined front suffix
  obtain ⟨h⟩ := appendIff (body := body) (Gamma := [A]) H M W front suffix joined c
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualOriginalUniverseInternalWorkCons :
    OriginalUniverseDecoderInternalAcceptanceTargets.ActualOriginalUniverseInternalWorkCons := by
  intro body H M W alpha work request suffix singleton c
  let A := StepCons work request suffix ⊓ StepCons singleton request z
  have hh : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := consIff H M W work request suffix singleton c (andLeft hh) (andRight hh)
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceAppendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptanceAppendProof
