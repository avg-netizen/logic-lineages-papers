module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceLambdaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootFrameProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceRootStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceAcceptanceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationListProof
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

open InternalAcceptanceSupportProof InternalApplicationValidityStackAppendListProof
open OriginalHereditaryValidityInternalRecurrenceFuelWorkAppendProof

theorem twoFrameIff (s t m : Program 2)
    (joined suffix fnFrame argFrame fn arg parameter : OTerm alpha)
    (hj : Nonempty (Derivation body Gamma (WorkCons joined fnFrame suffix)))
    (hs : Nonempty (Derivation body Gamma (WorkCons suffix argFrame z)))
    (hf : Nonempty (Derivation body Gamma (FrameGraph fnFrame fn parameter)))
    (ha : Nonempty (Derivation body Gamma (FrameGraph argFrame arg parameter))) :
    Nonempty (Derivation body Gamma
      ((WorkAccepted s t m joined).iff
        (graph2 (validator s t m) (numeral 1) fn parameter ⊓
          graph2 (validator s t m) (numeral 1) arg parameter))) := by
  apply programCases InternalListCodec.consCode (Fin.cons fnFrame (Fin.cons z Fin.elim0)) _
  intro beta j Delta front inc hfront
  change Nonempty (Derivation body Delta
    (((WorkAccepted s t m joined).relabel j).iff
      (((graph2 (validator s t m) (numeral 1) fn parameter).relabel j) ⊓
        ((graph2 (validator s t m) (numeral 1) arg parameter).relabel j))))
  simp only [OriginalHereditaryValidityInternalRecurrenceIterationSyntaxProof.workAcceptedRename,
    graph2Rename,oneRename]
  simp only [InternalRecursionGraphStepSyntaxProof.consTermRename,
    InternalControlGraphSupportProof.emptyRename,zRelabel] at hfront
  have hj' := renameInto hj j Delta inc
  have hs' := renameInto hs j Delta inc
  have hf' := renameInto hf j Delta inc
  have ha' := renameInto ha j Delta inc
  simp only [WorkCons,graph2Rename,zRelabel] at hj' hs'
  simp only [FrameGraph,graph2Rename] at hf' ha'
  have happend := consBackward front (fnFrame.relabel j) z (suffix.relabel j) (suffix.relabel j)
    (joined.relabel j) hfront (appendZeroValue (suffix.relabel j)) hj'
  have hfn := singletonIff s t m front (fnFrame.relabel j) (fn.relabel j) (parameter.relabel j) hfront hf'
  have harg := singletonIff s t m (suffix.relabel j) (argFrame.relabel j)
    (arg.relabel j) (parameter.relabel j) hs' ha'
  let A := WorkAccepted s t m (joined.relabel j)
  let B := graph2 (validator s t m) (numeral 1) (fn.relabel j) (parameter.relabel j) ⊓
    graph2 (validator s t m) (numeral 1) (arg.relabel j) (parameter.relabel j)
  have forward : Nonempty (Derivation body (A :: Delta) B) := by
    have hh := appendForward s t m front (suffix.relabel j) (joined.relabel j) (withHyp happend A)
      (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
    obtain ⟨hfnA⟩ := withHyp hfn A
    obtain ⟨hargA⟩ := withHyp harg A
    obtain ⟨hh⟩ := hh
    exact ⟨Derivation.conjunctionIntroduction
      (Derivation.implicationElimination (Derivation.conjunctionLeft hfnA) (Derivation.conjunctionLeft hh))
      (Derivation.implicationElimination (Derivation.conjunctionLeft hargA) (Derivation.conjunctionRight hh))⟩
  have backward : Nonempty (Derivation body (B :: Delta) A) := by
    obtain ⟨hfnB⟩ := withHyp hfn B
    obtain ⟨hargB⟩ := withHyp harg B
    have hh : Derivation body (B :: Delta) B := Derivation.hypothesis List.mem_cons_self
    exact appendBackward s t m front (suffix.relabel j) (joined.relabel j) (withHyp happend B)
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hfnB) (Derivation.conjunctionLeft hh)⟩
      ⟨Derivation.implicationElimination (Derivation.conjunctionRight hargB) (Derivation.conjunctionRight hh)⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalRecurrenceApplicationListProof
