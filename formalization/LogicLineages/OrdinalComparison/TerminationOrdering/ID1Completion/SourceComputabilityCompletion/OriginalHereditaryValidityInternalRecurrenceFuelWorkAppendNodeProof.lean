module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendNodeProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalAcceptanceSupportProof InternalTagArithmeticSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalBranchProof
open OriginalHereditaryValidityInternalNodeProof OriginalHereditaryValidityInternalRejectSupportProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendDispatchProof
open InternalOriginalPairingOrderArithmeticProof (formulaCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem nodeTransfer (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state))) :
    Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) joinedState)) :=
  acceptFactors s t m joinedState raw parameter
    (frameRaw _ _ _ _ _ _ hjs) (frameParameter _ _ _ _ _ _ hjs)
    (recoverFactors s t m state raw parameter
      (frameRaw _ _ _ _ _ _ hs) (frameParameter _ _ _ _ _ _ hs) hn)

 theorem rejectedCoupling (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest suffix : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state).not)) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  let Q := graph1 (nodeCheck s t m) (numeral 1) joinedState
  have ha : Nonempty (Derivation body (Q :: Delta) (graph1 (nodeCheck s t m) (numeral 1) state)) :=
    nodeTransfer s t m joinedState state joinedWork work frame raw parameter joinedRest rest
      (withHyp hjs Q) (withHyp hs Q) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨ha⟩ := ha
  obtain ⟨hn'⟩ := withHyp hn Q
  have hjn : Nonempty (Derivation body Delta Q.not) :=
    ⟨Derivation.implicationIntroduction (Derivation.implicationElimination hn' ha)⟩
  exact coupledFailureIntro s t m state joinedState suffix
    (rejectNode s t m state (stateFrameLive _ _ _ _ _ _ hs) hn)
    (rejectNode s t m joinedState (stateFrameLive _ _ _ _ _ _ hjs) hjn)

 theorem acceptedCoupling (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest suffix : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state))) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  have hjn := nodeTransfer s t m state joinedState work joinedWork frame raw parameter rest joinedRest hs hjs hn
  apply programCases OriginalLambdaConstructor.tag (Fin.cons raw Fin.elim0) _
  intro beta j Theta tag hj htag
  rw [coupledRename]
  simp only [consTermRename,emptyRename] at htag
  have hs' := renameInto hs j Theta hj
  have hjs' := renameInto hjs j Theta hj
  rw [stateFrameRename] at hs' hjs'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hn' := renameInto hn j Theta hj
  have hjn' := renameInto hjn j Theta hj
  simp only [graph1Rename,oneRename] at hn' hjn'
  exact tagCoupling s t m (state.relabel j) (joinedState.relabel j) (work.relabel j)
    (joinedWork.relabel j) (frame.relabel j) (raw.relabel j) (parameter.relabel j)
    (rest.relabel j) (joinedRest.relabel j) (suffix.relabel j) tag hs' hjs' ha' hn' hjn' htag

 theorem nodeCoupling (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest suffix : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix))) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  apply formulaCases (graph1 (nodeCheck s t m) (numeral 1) state)
  · exact acceptedCoupling s t m state joinedState work joinedWork frame raw parameter rest joinedRest suffix
      (withHyp hs _) (withHyp hjs _) (withHyp ha _) ⟨Derivation.hypothesis List.mem_cons_self⟩
  · exact rejectedCoupling s t m state joinedState work joinedWork frame raw parameter rest joinedRest suffix
      (withHyp hs _) (withHyp hjs _) ⟨Derivation.hypothesis List.mem_cons_self⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendNodeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendNodeProof
