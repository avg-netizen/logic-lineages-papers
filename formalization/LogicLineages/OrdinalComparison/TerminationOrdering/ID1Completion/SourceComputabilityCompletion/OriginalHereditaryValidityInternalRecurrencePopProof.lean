module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPopProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrencePopProof
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

open OriginalHereditaryValidityInternalPopProof
open OriginalHereditaryValidityInternalRecurrenceIterationWorkProof
open OriginalHereditaryValidityInternalRecurrenceIterationTerminalProof

theorem popAtFrame (s t m : Program 2) (state workCode frame raw parameter payload tag : OTerm alpha)
    (hs : Nonempty (Derivation body Gamma (StateFrame state workCode frame raw parameter z)))
    (hp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload raw)))
    (hn : Nonempty (Derivation body Gamma (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag tag raw)))
    (h2 : Nonempty (Derivation body Gamma (equal tag (numeral 2)).not))
    (h1 : Nonempty (Derivation body Gamma (equal tag (numeral 1)).not)) :
    Nonempty (Derivation body Gamma (graph2 (validator s t m) (numeral 1) raw parameter)) := by
  have hstep := popBackward s t m state workCode frame raw parameter z tag (numeral 2)
    hs hn ht h2 h1 successPair
  obtain ⟨hroot⟩ := rootAtNext s t m state workCode frame raw parameter payload (numeral 2) z
    hs hp hstep successPair
  obtain ⟨hnil⟩ := acceptedIntro s t m z z
    OriginalHereditaryValidityInternalRecurrenceFuelSupportProof.nilValue (nilSuccessful s t m z)
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hroot) hnil⟩

theorem popRecurrence (s t m : Program 2) (raw parameter tag : OTerm alpha)
    (hn : Nonempty (Derivation body Gamma (NodeFactors s t m raw parameter)))
    (ht : Nonempty (Derivation body Gamma (graph1 OriginalLambdaConstructor.tag tag raw)))
    (h2 : Nonempty (Derivation body Gamma (equal tag (numeral 2)).not))
    (h1 : Nonempty (Derivation body Gamma (equal tag (numeral 1)).not)) :
    Nonempty (Derivation body Gamma (graph2 (validator s t m) (numeral 1) raw parameter)) := by
  apply rootFrameCases raw parameter _
  intro beta j Delta state workCode frame payload hj hi hs hp
  simp only [graph2Rename,oneRename]
  have hn' := renameInto hn j Delta hj
  rw [factorsRename] at hn'
  have ht' := renameInto ht j Delta hj
  rw [graph1Rename] at ht'
  have h2' := renameInto h2 j Delta hj
  have h1' := renameInto h1 j Delta hj
  change Nonempty (Derivation body Delta ((equal tag (numeral 2)).relabel j).not) at h2'
  change Nonempty (Derivation body Delta ((equal tag (numeral 1)).relabel j).not) at h1'
  simp only [equalEqn,eqnRename,numeral,
    InternalTagArithmeticSyntaxProof.sucRelabel,zRelabel] at h2' h1'
  exact popAtFrame s t m state workCode frame (raw.relabel j) (parameter.relabel j) payload
    (tag.relabel j) hs hp
    (acceptFactors s t m state (raw.relabel j) (parameter.relabel j)
      (frameRaw _ _ _ _ _ _ hs) (frameParameter _ _ _ _ _ _ hs) hn') ht' (by simpa only [equalEqn,numeral] using h2')
      (by simpa only [equalEqn,numeral] using h1')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrencePopProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrencePopProof
