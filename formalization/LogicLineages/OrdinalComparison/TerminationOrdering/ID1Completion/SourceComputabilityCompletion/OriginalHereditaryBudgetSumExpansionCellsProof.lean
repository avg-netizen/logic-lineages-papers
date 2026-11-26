module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumRecurrenceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphExtensionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetDepthStatementChecks
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumExpansionCellsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof (congSuc)
open InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof (orderRight)
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalHereditaryBudgetSumBound OriginalHereditaryBudgetSumBoundSyntaxProof
open InternalClosedPrograms
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof
open OriginalHereditaryBudgetSumBoundCellsProof

theorem cellAt (parent jobs count depth branching previous index child value : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight (suc depth) parent)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count jobs)))
 (hp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget previous depth branching)))
 (hf : Nonempty (Derivation body Delta (cellFields count jobs branching index child value))) :
 Nonempty (Derivation body Delta (ltF value (suc previous))) := by
 apply programCases OriginalHereditaryFuelProgram.weight (Fin.cons child Fin.elim0) _
 intro beta j Theta childWeight hj hc
 simp only [consTermRename,emptyRename] at hc
 have he' := renameInto he j Theta hj
 have hw' := renameInto hw j Theta hj
 have hl' := renameInto hl j Theta hj
 have hp' := renameInto hp j Theta hj
 simp only [graph1Rename,graph2Rename,lengthRename,sucRelabel] at he' hw' hl' hp'
 have hb := renameInto (InternalApplicationStepPeelSupportProof.andLeft hf) j Theta hj
 simp only [Below,orderRename] at hb
 have hlookup := renameInto (InternalApplicationStepPeelSupportProof.andLeft (InternalApplicationStepPeelSupportProof.andRight hf)) j Theta hj
 rw [graph2Rename] at hlookup
 have hvalue := renameInto (InternalApplicationStepPeelSupportProof.andRight (InternalApplicationStepPeelSupportProof.andRight hf)) j Theta hj
 rw [graph2Rename] at hvalue
 have hless := OriginalHereditaryInternalExpansionStatementChecks.actualLookupDecrease body beta Theta
   (parent.relabel j) (jobs.relabel j) (count.relabel j) (index.relabel j) (child.relabel j)
   (suc (depth.relabel j)) childWeight he' hl' hb hlookup hw' hc
 have hbudget := OriginalHereditaryBudgetSumRecurrenceProof.jobRecover
   (child.relabel j) (branching.relabel j) childWeight (value.relabel j) hc hvalue
 simp only [orderRename,sucRelabel]
 exact OriginalHereditaryBudgetDepthStatementChecks.actualMonotone body beta Theta
   (depth.relabel j) childWeight (branching.relabel j) (value.relabel j) (previous.relabel j)
   hless hbudget hp'

theorem cells (parent jobs count depth branching previous : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight (suc depth) parent)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count jobs)))
 (hp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget previous depth branching))) :
 Nonempty (Derivation body Delta (CellsBound count jobs branching previous)) := by
 unfold CellsBound
 apply InternalClosedProgramsBindingProof.actualFiniteUniversalIntroduction body alpha 3 Delta
 let index : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let child : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let value : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := cellFields (count.relabel Sum.inl) (jobs.relabel Sum.inl) (branching.relabel Sum.inl) index child value
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
   intro f hf
   exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have he' := renameInto he Sum.inl Theta inc
 have hw' := renameInto hw Sum.inl Theta inc
 have hl' := renameInto hl Sum.inl Theta inc
 have hp' := renameInto hp Sum.inl Theta inc
 simp only [graph1Rename,graph2Rename,lengthRename,sucRelabel] at he' hw' hl' hp'
 obtain ⟨h⟩ := cellAt (parent.relabel Sum.inl) (jobs.relabel Sum.inl) (count.relabel Sum.inl)
   (depth.relabel Sum.inl) (branching.relabel Sum.inl) (previous.relabel Sum.inl) index child value
   he' hw' hl' hp' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumExpansionCellsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumExpansionCellsProof
