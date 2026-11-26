module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTransportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowBindingProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowStructuralProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalRecursionGraphStepSyntaxProof
open OriginalContextInsertion OriginalContextInsertionLengthProof
open OriginalContextInsertionSyntaxProof (lengthRename)
open OriginalHereditaryInternalAgenda OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalAgendaBindingProof OriginalHereditaryInternalAgendaTransportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open OriginalHereditaryInternalJobRow OriginalHereditaryInternalJobRowSyntaxProof OriginalHereditaryInternalJobRowBindingProof
theorem tail (H : Program 1) (M W : Program 2) (c B work head rest : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Jobs H M W c B work)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work head rest))) :
 Nonempty (Derivation body Delta (Jobs H M W c B rest)) := by
 apply jobsIntro H M W c B rest
 intro beta j Theta count index frame hinc hf
 have ha' := renameInto ha j Theta hinc
 have hc' := renameInto hc j Theta hinc
 rw [jobsRename] at ha'
 rw [graph2Rename] at hc'
 have hl := lengthCons (work.relabel j) (head.relabel j) (rest.relabel j) count hc' (andLeft hf)
 have hb := InternalRecursionGraphExtensionSupportProof.successorOrder index count (andLeft (andRight hf))
 obtain ⟨hi⟩ := OriginalAllPositionContextDeleteDropProof.lookupConsIff (work.relabel j) (head.relabel j) (rest.relabel j) index frame hc'
 obtain ⟨hv⟩ := andRight (andRight hf)
 have hlk := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight hi) hv)
 exact jobsApply H M W (c.relabel j) (B.relabel j) (work.relabel j) (suc count) (suc index) frame ha' (andIntro hl (andIntro hb hlk))

theorem head (H : Program 1) (M W : Program 2) (c B work head rest : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (Jobs H M W c B work)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode work head rest))) :
 Nonempty (Derivation body Delta (Job H M W c B head)) := by
 apply InternalAcceptanceSupportProof.programCases length (Fin.cons rest Fin.elim0) _
 intro beta j Theta count hinc hl
 simp only [consTermRename,emptyRename] at hl
 have ha' := renameInto ha j Theta hinc
 have hc' := renameInto hc j Theta hinc
 rw [jobsRename] at ha'
 rw [graph2Rename] at hc'
 rw [jobRename]
 exact jobsApply H M W (c.relabel j) (B.relabel j) (work.relabel j) (suc count) z (head.relabel j) ha'
  (andIntro (lengthCons (work.relabel j) (head.relabel j) (rest.relabel j) count hc' hl)
   (andIntro (OriginalHereditaryBudgetSumBoundCellsProof.zeroBound count)
    (OriginalAllPositionContextDeleteBaseProof.lookupZero (work.relabel j) (head.relabel j) (rest.relabel j) hc')))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowStructuralProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowStructuralProof
