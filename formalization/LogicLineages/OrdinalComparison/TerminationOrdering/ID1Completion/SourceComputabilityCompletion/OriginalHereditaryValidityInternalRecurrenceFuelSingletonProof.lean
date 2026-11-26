module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationSaturationSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem singletonAt (s t m : Program 2) (work frame raw parameter payload state : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (WorkCons work frame z)))
    (hf : Nonempty (Derivation body Delta (FrameGraph frame raw parameter)))
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload raw)))
    (hs : Nonempty (Derivation body Delta (StateGraph state (numeral 1) work))) :
    Nonempty (Derivation body Delta
      ((WorkAccepted s t m work).iff (graph2 (validator s t m) (numeral 1) raw parameter))) := by
  let A := WorkAccepted s t m work
  let Q := graph2 (validator s t m) (numeral 1) raw parameter
  have hw := singletonWeight work frame raw parameter payload hc hf hp
  have hi := initialAtSingleton state work frame raw parameter hs hc hf
  have hcount := fuelAtPayload raw parameter payload hp
  have forward : Nonempty (Derivation body (A :: Delta) Q) := by
    have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hsuccess := acceptedAtOwnFuel s t m (suc payload) work (withHyp hw A) ha
    have hiter := workRunAt s t m (numeral 2) (suc payload) work state (withHyp hs A) hsuccess
    exact runSuccessValidator s t m raw parameter
      (binaryValue (iterate s t m) fuel initial (numeral 2) (suc payload) state
        (Fin.cons raw (Fin.cons parameter Fin.elim0)) hiter (withHyp hcount A) (withHyp hi A))
  have backward : Nonempty (Derivation body (Q :: Delta) A) := by
    have hrun := validatorRunSuccess s t m raw parameter
      (show Nonempty (Derivation body (Q :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    have hiter := binaryRecover (iterate s t m) fuel initial (numeral 2) (suc payload) state
      (Fin.cons raw (Fin.cons parameter Fin.elim0)) hrun (withHyp hcount Q) (withHyp hi Q)
    exact acceptedIntro s t m work (suc payload) (withHyp hw Q)
      (workRunIntro s t m (numeral 2) (suc payload) work state (withHyp hs Q) hiter)
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

 theorem singletonIff (s t m : Program 2) (work frame raw parameter : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (WorkCons work frame z)))
    (hf : Nonempty (Derivation body Delta (FrameGraph frame raw parameter))) :
    Nonempty (Derivation body Delta
      ((WorkAccepted s t m work).iff (graph2 (validator s t m) (numeral 1) raw parameter))) := by
  let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),
    pairOf (InternalLessThan.constantOne 2) (.projection 1)]
  let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons work Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  change Nonempty (Derivation body Theta
    (((WorkAccepted s t m work).relabel j).iff
      ((graph2 (validator s t m) (numeral 1) raw parameter).relabel j)))
  simp only [workAcceptedRename,graph2Rename,oneRename]
  simp only [xs,consTermRename,emptyRename] at hq
  have hc' := renameInto hc j Theta hj
  simp only [WorkCons,graph2Rename,zRelabel] at hc'
  have hf' := renameInto hf j Theta hj
  simp only [FrameGraph,graph2Rename] at hf'
  let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel j) (Fin.cons (work.relabel j) Fin.elim0)
  have hp := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (raw.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have hs := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 2) (.projection 1)
    (ys 1) (numeral 1) (work.relabel j) xx (hq 1)
    (InternalLessThanSupportProof.oneConstantValue xx) (projectionValue 1 xx)
  exact singletonAt s t m (work.relabel j) (frame.relabel j) (raw.relabel j)
    (parameter.relabel j) (ys 0) (ys 1) hc' hf' hp hs

 theorem actualOriginalHereditaryInternalSingletonValidator :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalSingletonValidator := by
  intro body s t m alpha work frame raw parameter
  let C := WorkCons work frame z ⊓ FrameGraph frame raw parameter
  have h : Nonempty (Derivation body [C] C) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨d⟩ := singletonIff s t m work frame raw parameter (andLeft h) (andRight h)
  exact ⟨Derivation.implicationIntroduction d⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelSingletonProof
