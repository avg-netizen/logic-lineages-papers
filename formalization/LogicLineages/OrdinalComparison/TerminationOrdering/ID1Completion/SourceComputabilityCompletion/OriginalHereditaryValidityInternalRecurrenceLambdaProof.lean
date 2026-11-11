module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidity OriginalHereditaryValidityInternal OriginalHereditaryValidityInternalRecurrence
open OriginalHereditaryValidityInternalStateSupportProof OriginalHereditaryValidityInternalBranchProof
open OriginalHereditaryValidityInternalNodeSyntaxProof OriginalHereditaryValidityInternalNodeProof
open OriginalHereditaryValidityInternalRecurrenceFuelSupportProof (withHyp)
open OriginalHereditaryValidityInternalRecurrenceFuelSingletonSupportProof
open OriginalHereditaryValidityInternalRecurrenceFuelSingletonProof
open OriginalHereditaryValidityInternalRecurrenceRootFrameProof OriginalHereditaryValidityInternalRecurrenceRootStepProof
open OriginalHereditaryValidityInternalRecurrenceLambdaSyntaxProof OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

theorem lambdaAtFrame (s t m : Program 2) (state workCode frame raw parameter payload : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff (RootLambdaChild s t m raw parameter))) := by
  have hi := initialAtSingleton state workCode frame raw parameter
    (andLeft hs) (andLeft (andRight hs)) (andRight (andRight hs))
  apply lambdaSuccessorCases s t m state workCode frame raw parameter _ hs hn ht
  intro beta j Delta child childParameterCode next nextWork nextFrame hj hc hcp he hnext htransition
  change Nonempty (Derivation body Delta
    (((graph2 (validator s t m) (numeral 1) raw parameter).relabel j).iff
      ((RootLambdaChild s t m raw parameter).relabel j)))
  simp only [graph2Rename,oneRename,rootLambdaRename]
  have hs' := renameInto hs j Delta hj
  simp only [stateFrameRename,zRelabel] at hs'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  have hi' := renameInto hi j Delta hj
  rw [graph2Rename] at hi'
  have hroot := rootAtNext s t m (state.relabel j) (workCode.relabel j) (frame.relabel j)
    (raw.relabel j) (parameter.relabel j) (payload.relabel j) next nextWork hs' hp' htransition (andLeft hnext)
  have hsingle := singletonIff s t m nextWork nextFrame child childParameterCode
    (andLeft (andRight hnext)) (andRight (andRight hnext))
  let A := graph2 (validator s t m) (numeral 1) (raw.relabel j) (parameter.relabel j)
  let B := RootLambdaChild s t m (raw.relabel j) (parameter.relabel j)
  have forward : Nonempty (Derivation body (A :: Delta) B) := by
    obtain ⟨hrootA⟩ := withHyp hroot A
    obtain ⟨hsingleA⟩ := withHyp hsingle A
    have hwork := Derivation.implicationElimination (Derivation.conjunctionLeft hrootA)
      (Derivation.hypothesis List.mem_cons_self)
    have hchild := Derivation.implicationElimination (Derivation.conjunctionLeft hsingleA) hwork
    exact rootLambdaIntro s t m (raw.relabel j) (parameter.relabel j) (state.relabel j) child childParameterCode
      (andIntro (withHyp hi' A)
        (andIntro (andIntro (withHyp hc A) (withHyp he A)) (andIntro (withHyp hcp A) ⟨hchild⟩)))
  have backward : Nonempty (Derivation body (B :: Delta) A) := by
    have hchild := rootLambdaAt s t m (raw.relabel j) (parameter.relabel j) (state.relabel j)
      child childParameterCode (withHyp hi' B) (withHyp hc B) (withHyp hcp B)
      (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hchild⟩ := hchild
    obtain ⟨hsingleB⟩ := withHyp hsingle B
    obtain ⟨hrootB⟩ := withHyp hroot B
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hrootB)
      (Derivation.implicationElimination (Derivation.conjunctionRight hsingleB) hchild)⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem lambdaRecurrence (s t m : Program 2) (raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 1) raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff (RootLambdaChild s t m raw parameter))) := by
  apply rootFrameCases raw parameter _
  intro beta j Delta state workCode frame payload hj hi hs hp
  change Nonempty (Derivation body Delta
    (((graph2 (validator s t m) (numeral 1) raw parameter).relabel j).iff
      ((RootLambdaChild s t m raw parameter).relabel j)))
  simp only [graph2Rename,oneRename,rootLambdaRename]
  have hn' := renameInto hn j Delta hj
  rw [factorsRename] at hn'
  have ht' := renameInto ht j Delta hj
  simp only [graph1Rename,oneRename] at ht'
  exact lambdaAtFrame s t m state workCode frame (raw.relabel j) (parameter.relabel j) payload hs hp
    (acceptFactors s t m state (raw.relabel j) (parameter.relabel j)
      (frameRaw _ _ _ _ _ _ hs) (frameParameter _ _ _ _ _ _ hs) hn') ht'

theorem actualOriginalHereditaryInternalLambdaChildClosure :
    OriginalHereditaryValidityInternalRecurrenceTargets.ActualOriginalHereditaryInternalLambdaChildClosure := by
  intro body s t m alpha raw parameter
  let A := graph2 (validator s t m) (numeral 1) raw parameter ⊓
    graph1 OriginalLambdaConstructor.tag (numeral 1) raw
  have ha : Nonempty (Derivation body [A] A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hv := andLeft ha
  obtain ⟨hr⟩ := lambdaRecurrence s t m raw parameter (acceptanceFactors s t m raw parameter hv) (andRight ha)
  obtain ⟨hv⟩ := hv
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationElimination (Derivation.conjunctionLeft hr) hv)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaProof
