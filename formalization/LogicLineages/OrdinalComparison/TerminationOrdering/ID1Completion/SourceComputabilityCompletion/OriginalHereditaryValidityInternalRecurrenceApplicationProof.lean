module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationProof
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
open OriginalHereditaryValidityInternalRecurrenceApplicationSyntaxProof OriginalHereditaryValidityInternalRecurrenceApplicationSupportProof
open OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

open OriginalHereditaryValidityInternalRecurrenceApplicationListProof

theorem applicationAtFrame (s t m : Program 2) (state workCode frame raw parameter payload : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 2) raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff (RootApplicationChildren s t m raw parameter))) := by
  have hi := initialAtSingleton state workCode frame raw parameter
    (andLeft hs) (andLeft (andRight hs)) (andRight (andRight hs))
  apply applicationSuccessorCases s t m state workCode frame raw parameter _ hs hn ht
  intro beta j Delta fn arg next nextWork suffix fnFrame argFrame hj hfn harg fields htransition
  change Nonempty (Derivation body Delta
    (((graph2 (validator s t m) (numeral 1) raw parameter).relabel j).iff
      ((RootApplicationChildren s t m raw parameter).relabel j)))
  simp only [graph2Rename,oneRename,rootApplicationRename]
  have hs' := renameInto hs j Delta hj
  simp only [stateFrameRename,zRelabel] at hs'
  have hp' := renameInto hp j Delta hj
  rw [graph1Rename] at hp'
  have hi' := renameInto hi j Delta hj
  rw [graph2Rename] at hi'
  have hroot := rootAtNext s t m (state.relabel j) (workCode.relabel j) (frame.relabel j)
    (raw.relabel j) (parameter.relabel j) (payload.relabel j) next nextWork hs' hp' htransition (andLeft fields)
  have hchildren := twoFrameIff s t m nextWork suffix fnFrame argFrame fn arg (parameter.relabel j)
    (andLeft (andRight fields)) (andLeft (andRight (andRight (andRight fields))))
    (andLeft (andRight (andRight fields))) (andRight (andRight (andRight (andRight fields))))
  let A := graph2 (validator s t m) (numeral 1) (raw.relabel j) (parameter.relabel j)
  let B := RootApplicationChildren s t m (raw.relabel j) (parameter.relabel j)
  have forward : Nonempty (Derivation body (A :: Delta) B) := by
    obtain ⟨hrootA⟩ := withHyp hroot A
    obtain ⟨hchildrenA⟩ := withHyp hchildren A
    have hwork := Derivation.implicationElimination (Derivation.conjunctionLeft hrootA)
      (Derivation.hypothesis List.mem_cons_self)
    have hv := Derivation.implicationElimination (Derivation.conjunctionLeft hchildrenA) hwork
    exact rootApplicationIntro s t m (raw.relabel j) (parameter.relabel j) (state.relabel j) fn arg
      (andIntro (withHyp hi' A) (andIntro (withHyp hfn A)
        (andIntro (andIntro (withHyp harg A) ⟨Derivation.conjunctionLeft hv⟩)
          ⟨Derivation.conjunctionRight hv⟩)))
  have backward : Nonempty (Derivation body (B :: Delta) A) := by
    obtain ⟨hv⟩ := rootApplicationAt s t m (raw.relabel j) (parameter.relabel j) (state.relabel j)
      fn arg (withHyp hi' B) (withHyp hfn B) (withHyp harg B)
      (show Nonempty (Derivation body (B :: Delta) B) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hchildrenB⟩ := withHyp hchildren B
    obtain ⟨hrootB⟩ := withHyp hroot B
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hrootB)
      (Derivation.implicationElimination (Derivation.conjunctionRight hchildrenB) hv)⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem applicationRecurrence (s t m : Program 2) (raw parameter : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag (numeral 2) raw))) :
    Nonempty (Derivation body Gamma
      ((graph2 (validator s t m) (numeral 1) raw parameter).iff (RootApplicationChildren s t m raw parameter))) := by
  apply rootFrameCases raw parameter _
  intro beta j Delta state workCode frame payload hj hi hs hp
  change Nonempty (Derivation body Delta
    (((graph2 (validator s t m) (numeral 1) raw parameter).relabel j).iff
      ((RootApplicationChildren s t m raw parameter).relabel j)))
  simp only [graph2Rename,oneRename,rootApplicationRename]
  have hn' := renameInto hn j Delta hj
  rw [factorsRename] at hn'
  have ht' := renameInto ht j Delta hj
  simp only [graph1Rename,numeral,InternalTagArithmeticSyntaxProof.sucRelabel,zRelabel] at ht'
  exact applicationAtFrame s t m state workCode frame (raw.relabel j) (parameter.relabel j) payload hs hp
    (acceptFactors s t m state (raw.relabel j) (parameter.relabel j)
      (frameRaw _ _ _ _ _ _ hs) (frameParameter _ _ _ _ _ _ hs) hn') ht'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationProof
