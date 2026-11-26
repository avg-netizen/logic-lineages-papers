module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalBranchProof
open OriginalHereditaryValidityInternalResultSyntaxProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendSelectorProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem applicationCoupling (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest suffix : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (hjn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) joinedState)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) raw))) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  apply queryCases ![currentFunction,currentArgument] (Fin.cons state Fin.elim0) _
  intro beta j ys Theta hj hq
  rw [coupledRename]
  simp only [consTermRename,emptyRename] at hq
  have hs' := renameInto hs j Theta hj
  have hjs' := renameInto hjs j Theta hj
  rw [stateFrameRename] at hs' hjs'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hn' := renameInto hn j Theta hj
  have hjn' := renameInto hjn j Theta hj
  simp only [graph1Rename,oneRename] at hn' hjn'
  have htag' := renameInto htag j Theta hj
  simp only [graph1Rename,numeral,sucRelabel,zRelabel] at htag'
  have hr := frameRaw _ _ _ _ _ _ hs'
  have hjr := frameRaw _ _ _ _ _ _ hjs'
  have hp := frameParameter _ _ _ _ _ _ hs'
  have hjp := frameParameter _ _ _ _ _ _ hjs'
  have hjf := functionShared body beta Theta (state.relabel j) (joinedState.relabel j)
    (raw.relabel j) (parameter.relabel j) (ys 0) hr hjr hp hjp (hq 0)
  have hja := argumentShared body beta Theta (state.relabel j) (joinedState.relabel j)
    (raw.relabel j) (parameter.relabel j) (ys 1) hr hjr hp hjp (hq 1)
  apply applicationPushCases (ys 0) (ys 1) (parameter.relabel j) (rest.relabel j)
    (joinedRest.relabel j) (suffix.relabel j) _ ha'
  intro gamma k Xi frontNext joinedNext nextState joinedNextState hk happ hnext hjnext hpush hjpush
  rw [coupledRename]
  have hs'' := renameInto hs' k Xi hk
  have hjs'' := renameInto hjs' k Xi hk
  rw [stateFrameRename] at hs'' hjs''
  have hn'' := renameInto hn' k Xi hk
  have hjn'' := renameInto hjn' k Xi hk
  simp only [graph1Rename,oneRename] at hn'' hjn''
  have htag'' := renameInto htag' k Xi hk
  simp only [graph1Rename,numeral,sucRelabel,zRelabel] at htag''
  have hf := renameInto (hq 0) k Xi hk
  have harg := renameInto (hq 1) k Xi hk
  have hjf' := renameInto hjf k Xi hk
  have hja' := renameInto hja k Xi hk
  rw [graph1Rename] at hf harg hjf' hja'
  have hresult := applicationResultIntro ((state.relabel j).relabel k) nextState
    ((parameter.relabel j).relabel k) ((rest.relabel j).relabel k) ((ys 0).relabel k) ((ys 1).relabel k)
    (andIntro hf (andIntro harg hpush))
  have hjresult := applicationResultIntro ((joinedState.relabel j).relabel k) joinedNextState
    ((parameter.relabel j).relabel k) ((joinedRest.relabel j).relabel k) ((ys 0).relabel k) ((ys 1).relabel k)
    (andIntro hjf' (andIntro hja' hjpush))
  have ht := OriginalHereditaryValidityInternalApplicationProof.applicationBackward s t m
    ((state.relabel j).relabel k) ((work.relabel j).relabel k) ((frame.relabel j).relabel k)
    ((raw.relabel j).relabel k) ((parameter.relabel j).relabel k) ((rest.relabel j).relabel k)
    nextState hs'' hn'' htag'' hresult
  have hjt := OriginalHereditaryValidityInternalApplicationProof.applicationBackward s t m
    ((joinedState.relabel j).relabel k) ((joinedWork.relabel j).relabel k) ((frame.relabel j).relabel k)
    ((raw.relabel j).relabel k) ((parameter.relabel j).relabel k) ((joinedRest.relabel j).relabel k)
    joinedNextState hjs'' hjn'' htag'' hjresult
  exact coupledLiveIntro s t m ((state.relabel j).relabel k) ((joinedState.relabel j).relabel k)
    ((suffix.relabel j).relabel k) frontNext joinedNext nextState joinedNextState
    (andIntro happ (andIntro hnext (andIntro hjnext (andIntro ht hjt))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendApplicationProof
