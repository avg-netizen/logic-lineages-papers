module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumExpansionCellsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open InternalSliceInductionSyntaxProof (eqnRename)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem impossibleCons (parent jobs head tail : OTerm alpha) (psi : Formula alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight z parent)))
 (hc : Nonempty (Derivation body Delta (consGraph jobs head tail))) :
 Nonempty (Derivation body Delta psi) := by
 let qs : Fin 2 → Program 2 := ![
   .composition length (fun _ : Fin 1 => .projection 1),
   .composition OriginalHereditaryFuelProgram.weight (fun _ : Fin 1 => .projection 0)]
 let xs : Fin 2 → OTerm alpha := Fin.cons head (Fin.cons tail Fin.elim0)
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hj hq
 let xx : Fin 2 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (tail.relabel j) Fin.elim0)
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have ht := unaryRecover length (.projection 1) (ys 0) (tail.relabel j) xx (hq 0) (projectionValue 1 xx)
 have hweight := unaryRecover OriginalHereditaryFuelProgram.weight (.projection 0) (ys 1) (head.relabel j) xx (hq 1) (projectionValue 0 xx)
 have he' := renameInto he j Theta hj
 have hw' := renameInto hw j Theta hj
 have hc' := renameInto hc j Theta hj
 simp only [graph1Rename,zRelabel] at he' hw'
 rw [consGraphRename] at hc'
 have hl := lengthCons (jobs.relabel j) (head.relabel j) (tail.relabel j) (ys 0) hc' ht
 have hlookup := OriginalAllPositionContextDeleteBaseProof.lookupZero (jobs.relabel j) (head.relabel j) (tail.relabel j) hc'
 obtain ⟨hbad⟩ := OriginalHereditaryInternalExpansionStatementChecks.actualLookupDecrease body beta Theta
   (parent.relabel j) (jobs.relabel j) (suc (ys 0)) z (head.relabel j) z (ys 1)
   he' hl (OriginalHereditaryBudgetSumBoundCellsProof.zeroBound (ys 0)) hlookup hw' hweight
 obtain ⟨hn⟩ := InternalApplicationValidityStackAppendTransitionProof.notLessZero (body := body) (Gamma := Theta) (ys 1)
 exact ⟨Derivation.explosion (Derivation.implicationElimination hn hbad)⟩

theorem zeroJobs (parent jobs : OTerm alpha)
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight z parent))) :
 Nonempty (Derivation body Delta (eqn jobs z)) := by
 apply listCases jobs _ ⟨Derivation.hypothesis List.mem_cons_self⟩
 intro beta j Theta head tail hj hc
 have he' := renameInto he j Theta hj
 have hw' := renameInto hw j Theta hj
 simp only [graph1Rename,zRelabel] at he' hw'
 exact impossibleCons (parent.relabel j) (jobs.relabel j) head tail _ he' hw' hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumZeroProof
