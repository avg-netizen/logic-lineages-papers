module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumExpansionCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumZeroProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLengthStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumLocalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalOriginalOrderSyntaxProof
open InternalSquareRootArithmeticSupportProof (orderLeft orderRight)
open InternalUnpairReverseBoundsArithmeticProof (weakTrans)
open InternalMultiplicationLawsProof (mul)
open InternalRecursionGraphStepSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atSuccessor (parent jobs depth branching total parentBudget count previous : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight (suc depth) parent)))
 (hb : Nonempty (Derivation body Delta (ltF (suc (suc (suc depth))) (suc branching))))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum total jobs branching)))
 (hq : Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget parentBudget (suc depth) branching)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count jobs)))
 (hp : Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget previous depth branching))) :
 Nonempty (Derivation body Delta (ltF total parentBudget)) := by
 have hc := OriginalHereditaryBudgetSumExpansionCellsProof.cells parent jobs count depth branching previous he hw hl hp
 have hsum := OriginalHereditaryBudgetSumBoundStatementChecks.actualMajorization body alpha Delta count jobs branching previous total hl hc hs
 have hlength := OriginalHereditaryInternalExpansionLengthStatementChecks.actualLengthBound body alpha Delta
   parent jobs count (suc depth) he hl hw
 have hcount := weakTrans count (suc (suc (suc depth))) branching hlength hb
 have hproduct := OriginalHereditaryBudgetOrderArithmeticProof.mulWeakLeft count branching previous hcount
 obtain ⟨hbound⟩ := weakTrans total (mul count previous) (mul branching previous) hsum hproduct
 obtain ⟨heq⟩ := OriginalHereditaryBudgetInternalProof.actualSuccessorEquation body alpha Delta depth branching previous parentBudget hp hq
 exact ⟨orderRight total (symm heq) hbound⟩

theorem successorCase (parent jobs depth branching total parentBudget : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight (suc depth) parent)))
 (hb : Nonempty (Derivation body Delta (ltF (suc (suc (suc depth))) (suc branching))))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum total jobs branching)))
 (hq : Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget parentBudget (suc depth) branching))) :
 Nonempty (Derivation body Delta (ltF total parentBudget)) := by
 let qs : Fin 2 → Program 3 := ![
   .composition length (fun _ : Fin 1 => .projection 0),
   .composition OriginalHereditaryFuelProgram.budget ![.projection 1,.projection 2] ]
 let xs : Fin 3 → OTerm alpha := Fin.cons jobs (Fin.cons depth (Fin.cons branching Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hquery
 let xx : Fin 3 → OTerm beta := Fin.cons (jobs.relabel j) (Fin.cons (depth.relabel j) (Fin.cons (branching.relabel j) Fin.elim0))
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hquery
 have hl := unaryRecover length (.projection 0) (ys 0) (jobs.relabel j) xx (hquery 0) (projectionValue 0 xx)
 have hp := binaryRecover OriginalHereditaryFuelProgram.budget (.projection 1) (.projection 2)
   (ys 1) (depth.relabel j) (branching.relabel j) xx (hquery 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have he' := renameInto he j Theta hj
 have hw' := renameInto hw j Theta hj
 have hb' := renameInto hb j Theta hj
 have hs' := renameInto hs j Theta hj
 have hq' := renameInto hq j Theta hj
 simp only [graph1Rename,graph2Rename,orderRename,sucRelabel] at he' hw' hb' hs' hq'
 rw [orderRename]
 exact atSuccessor (parent.relabel j) (jobs.relabel j) (depth.relabel j) (branching.relabel j)
   (total.relabel j) (parentBudget.relabel j) (ys 0) (ys 1) he' hw' hb' hs' hq' hl hp

theorem zeroCase (parent jobs branching total parentBudget : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight z parent)))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum total jobs branching)))
 (hq : Nonempty (Derivation body Delta (graph2 OriginalHereditaryFuelProgram.budget parentBudget z branching))) :
 Nonempty (Derivation body Delta (ltF total parentBudget)) := by
 have hzero := OriginalHereditaryBudgetSumZeroProof.zeroJobs parent jobs he hw
 have hs0 := headTransport OriginalHereditaryBudgetSum.sum total jobs z (Fin.cons branching Fin.elim0) hzero hs
 obtain ⟨hse⟩ := valueUnique OriginalHereditaryBudgetSum.sum total z (Fin.cons z (Fin.cons branching Fin.elim0)) hs0
   (OriginalHereditaryBudgetSumRecurrenceProof.nilValue branching)
 obtain ⟨hqe⟩ := valueUnique OriginalHereditaryFuelProgram.budget parentBudget (suc z)
   (Fin.cons z (Fin.cons branching Fin.elim0)) hq (OriginalHereditaryBudgetInternalProof.actualZero body alpha Delta branching)
 obtain ⟨hz⟩ := OriginalHereditaryBudgetSumBoundCellsProof.zeroBound (body := body) (Delta := Delta) z
 exact ⟨orderRight total (symm hqe) (orderLeft (suc z) (symm hse) hz)⟩

theorem actualLocalBound : OriginalHereditaryBudgetSumTargets.ActualLocalBound := by
 intro body alpha Delta parent jobs weight branching total parentBudget he hw hb hs hq
 apply zeroSuccessorCases Delta weight _
 · let A := eqn weight z
   have hA : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hw0 := outputTransport OriginalHereditaryFuelProgram.weight weight z (Fin.cons parent Fin.elim0) hA (withHyp hw A)
   have hq0 := headTransport OriginalHereditaryFuelProgram.budget parentBudget weight z (Fin.cons branching Fin.elim0) hA (withHyp hq A)
   exact zeroCase parent jobs branching total parentBudget (withHyp he A) hw0 (withHyp hs A) hq0
 · intro beta j Theta depth hj hweight
   have he' := renameInto he j Theta hj
   have hw' := renameInto hw j Theta hj
   have hb' := renameInto hb j Theta hj
   have hs' := renameInto hs j Theta hj
   have hq' := renameInto hq j Theta hj
   simp only [graph1Rename,graph2Rename,orderRename,sucRelabel] at he' hw' hb' hs' hq'
   have hw1 := outputTransport OriginalHereditaryFuelProgram.weight (weight.relabel j) (suc depth)
     (Fin.cons (parent.relabel j) Fin.elim0) hweight hw'
   have hq1 := headTransport OriginalHereditaryFuelProgram.budget (parentBudget.relabel j) (weight.relabel j)
     (suc depth) (Fin.cons (branching.relabel j) Fin.elim0) hweight hq'
   obtain ⟨hh⟩ := hweight
   obtain ⟨hbb⟩ := hb'
   have hb1 := Nonempty.intro (orderLeft (suc (branching.relabel j)) (congSuc (congSuc hh)) hbb)
   rw [orderRename]
   exact successorCase (parent.relabel j) (jobs.relabel j) depth (branching.relabel j)
     (total.relabel j) (parentBudget.relabel j) he' hw1 hb1 hs' hq1
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumLocalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumLocalProof
