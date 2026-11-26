module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPopProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPopProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalHereditaryValidityInternalStateSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPushLambdaProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendCouplingSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

 theorem popCoupling (s t m : Program 2)
    (state joinedState work joinedWork frame raw parameter rest joinedRest suffix tag : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state work frame raw parameter rest)))
    (hjs : Nonempty (Derivation body Delta (StateFrame joinedState joinedWork frame raw parameter joinedRest)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joinedRest rest suffix)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (hjn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) joinedState)))
    (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw)))
    (h2 : Nonempty (Derivation body Delta (equal tag (numeral 2)).not))
    (h1 : Nonempty (Derivation body Delta (equal tag (numeral 1)).not)) :
    Nonempty (Derivation body Delta (CoupledStep s t m state joinedState suffix)) := by
  apply statePairCases rest joinedRest _
  intro beta j Theta nextState joinedNextState hj hnext hjnext
  rw [coupledRename]
  have hs' := renameInto hs j Theta hj
  have hjs' := renameInto hjs j Theta hj
  rw [stateFrameRename] at hs' hjs'
  have ha' := renameInto ha j Theta hj
  rw [graph2Rename] at ha'
  have hn' := renameInto hn j Theta hj
  have hjn' := renameInto hjn j Theta hj
  simp only [graph1Rename,oneRename] at hn' hjn'
  have htag' := renameInto htag j Theta hj
  rw [graph1Rename] at htag'
  have h2' := renameInto h2 j Theta hj
  have h1' := renameInto h1 j Theta hj
  change Nonempty (Derivation body Theta ((equal tag (numeral 2)).relabel j).not) at h2'
  change Nonempty (Derivation body Theta ((equal tag (numeral 1)).relabel j).not) at h1'
  simp only [equalEqn,eqnRelabel,numeral,sucRelabel,zRelabel] at h2' h1'
  have ht := OriginalHereditaryValidityInternalPopProof.popBackward s t m
    (state.relabel j) (work.relabel j) (frame.relabel j) (raw.relabel j) (parameter.relabel j)
    (rest.relabel j) (tag.relabel j) nextState hs' hn' htag'
    (by simpa only [equalEqn,numeral] using h2') (by simpa only [equalEqn,numeral] using h1') hnext
  have hjt := OriginalHereditaryValidityInternalPopProof.popBackward s t m
    (joinedState.relabel j) (joinedWork.relabel j) (frame.relabel j) (raw.relabel j) (parameter.relabel j)
    (joinedRest.relabel j) (tag.relabel j) joinedNextState hjs' hjn' htag'
    (by simpa only [equalEqn,numeral] using h2') (by simpa only [equalEqn,numeral] using h1') hjnext
  exact coupledLiveIntro s t m (state.relabel j) (joinedState.relabel j) (suffix.relabel j)
    (rest.relabel j) (joinedRest.relabel j) nextState joinedNextState
    (andIntro ha' (andIntro hnext (andIntro hjnext (andIntro ht hjt))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPopProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendPopProof
