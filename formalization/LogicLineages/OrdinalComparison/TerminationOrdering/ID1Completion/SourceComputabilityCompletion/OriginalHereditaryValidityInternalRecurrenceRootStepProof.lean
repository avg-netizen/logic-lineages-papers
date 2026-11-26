module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalStateSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (withHyp)
open OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
open OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationProof
open OriginalHereditaryValidityInternalRecurrenceIterationSaturationProof
open OriginalHereditaryValidityInternalRecurrenceRootBoundProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem rootAtNextFuel (s t m : Program 2)
    (state workCode frame raw parameter payload next nextWork nextFuel : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition s t m) next state)))
    (hn : Nonempty (Derivation body Gamma (StateGraph next (numeral 1) nextWork)))
    (hf : Nonempty (Derivation body Gamma (WorkFuelGraph nextFuel nextWork))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff (WorkAccepted s t m nextWork))) := by
  let A := graph2 (validator s t m) (numeral 1) raw parameter
  let B := WorkAccepted s t m nextWork
  have hi := initialAtSingleton state workCode frame raw parameter
    (andLeft hs) (andLeft (andRight hs)) (andRight (andRight hs))
  have hcount := fuelAtPayload raw parameter payload hp
  have hb := nextFuelBound s t m state workCode frame raw parameter payload next nextWork nextFuel hs hp ht hn hf
  have forward : Nonempty (Derivation body (A :: Gamma) B) := by
    have hv : Nonempty (Derivation body (A :: Gamma) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hrun := validatorRunSuccess s t m raw parameter hv
    have hiter := binaryRecover (iterate s t m) fuel initial (numeral 2) (suc payload) state
      (Fin.cons raw (Fin.cons parameter Fin.elim0)) hrun (withHyp hcount A) (withHyp hi A)
    have hrest := iterateAfterFirstRecover s t m payload state next (numeral 2) (withHyp ht A) hiter
    have hwork := workRunIntro s t m (numeral 2) payload nextWork next (withHyp hn A) hrest
    exact saturatedForward s t m nextFuel payload nextWork (withHyp hf A) (withHyp hb A) hwork
  have backward : Nonempty (Derivation body (B :: Gamma) A) := by
    have ha : Nonempty (Derivation body (B :: Gamma) B) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hwork := saturatedBackward s t m nextFuel payload nextWork (withHyp hf B) (withHyp hb B) ha
    have hrest := workRunAt s t m (numeral 2) payload nextWork next (withHyp hn B) hwork
    have hiter := iterateAfterFirst s t m payload state next (numeral 2) (withHyp ht B) hrest
    exact runSuccessValidator s t m raw parameter
      (binaryValue (iterate s t m) fuel initial (numeral 2) (suc payload) state
        (Fin.cons raw (Fin.cons parameter Fin.elim0)) hiter (withHyp hcount B) (withHyp hi B))
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

/-- At every actual live successor, parent acceptance is equivalent to
acceptance of the whole next worklist at its OWN computed payload fuel.
Its weight witness and sufficient bound are constructed internally. -/
theorem rootAtNext (s t m : Program 2)
    (state workCode frame raw parameter payload next nextWork : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (ht : Nonempty (Derivation body Gamma (graph1 (transition s t m) next state)))
    (hn : Nonempty (Derivation body Gamma (StateGraph next (numeral 1) nextWork))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff (WorkAccepted s t m nextWork))) := by
  apply programCases workFuel (Fin.cons nextWork Fin.elim0) _
  intro beta j Delta nextFuel hj hf
  change Nonempty (Derivation body Delta
    (((graph2 (validator s t m) (numeral 1) raw parameter).relabel j).iff
      ((WorkAccepted s t m nextWork).relabel j)))
  simp only [graph2Rename,oneRename,workAcceptedRename]
  simp only [consTermRename,emptyRename] at hf
  have hs' := renameInto hs j Delta hj
  simp only [stateFrameRename,zRelabel] at hs'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at ht'
  have hn' := renameInto hn j Delta hj
  simp only [StateGraph,graph2Rename,oneRename] at hn'
  exact rootAtNextFuel s t m (state.relabel j) (workCode.relabel j) (frame.relabel j)
    (raw.relabel j) (parameter.relabel j) (payload.relabel j) (next.relabel j)
    (nextWork.relabel j) nextFuel hs' hp' ht' hn' hf

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootStepProof
