module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialTaggedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialArithmeticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialVisitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalListCodecSupportProof (consGraph consGraphRename)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (ltF orderRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem atValues (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (parent visit returnFrame returnPayload jobs tagged rest work returnRest next branching weight before after : OTerm alpha) (q s r : OTerm alpha)
 (hvisit : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing visit z parent)))
 (hreturn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (suc z) returnPayload)))
 (hwork : Nonempty (Derivation body Delta (consGraph work visit rest)))
 (hrest : Nonempty (Derivation body Delta (consGraph returnRest returnFrame rest)))
 (hexp : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs parent)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append next tagged returnRest)))
 (hweight : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight parent)))
 (hbranch : Nonempty (Derivation body Delta (ltF (suc (suc weight)) (suc branching))))
 (hbefore : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda before work branching)))
 (hafter : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda after next branching)))
 (hq : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.jobBudget q parent branching)))
 (hs : Nonempty (Derivation body Delta (graph2 OriginalHereditaryBudgetSum.sum s jobs branching)))
 (hr : Nonempty (Derivation body Delta (graph2 OriginalHereditaryAgendaPotential.agenda r rest branching))) :
 Nonempty (Derivation body Delta (ltF after before)) := by
 have hp := OriginalHereditaryBudgetSumRecurrenceProof.jobRecover parent branching weight q hweight hq
 have hless := OriginalHereditaryBudgetSumStatementChecks.actualLocalBound body alpha Delta parent jobs weight branching s q
   hexp hweight hbranch hs hp
 have hcost := OriginalHereditaryAgendaPotentialFrameProof.visitCost visit parent branching q hvisit hq
 have heBefore := OriginalHereditaryAgendaPotentialRecurrenceProof.consEquation work visit rest branching (add q q) r before
   hwork hcost hr hbefore
 have hretcost := OriginalHereditaryAgendaPotentialFrameProof.returnCost returnFrame returnPayload branching hreturn
 have hret := OriginalHereditaryAgendaPotentialRecurrenceProof.consValue returnRest returnFrame rest branching (suc z) r
   hrest hretcost hr
 have htagged := OriginalHereditaryAgendaPotentialTaggedProof.actualTagged body alpha Delta jobs tagged branching s htag hs
 have hnext := OriginalHereditaryAgendaPotentialAppendProof.actualAppend body alpha Delta tagged returnRest next branching
   (add s s) (add (suc z) r) happend htagged hret
 have heAfter := valueUnique OriginalHereditaryAgendaPotential.agenda after (add (add s s) (add (suc z) r))
   (Fin.cons next (Fin.cons branching Fin.elim0)) hafter hnext
 exact InternalOriginalPairingOrderArithmeticProof.strictTransport after before _ _ heAfter heBefore
   (OriginalHereditaryAgendaPotentialArithmeticProof.replacementGap s q r hless)

theorem actualVisitReplacement : OriginalHereditaryAgendaPotentialTargets.VisitReplacement := by
 intro body alpha Delta parent visit returnFrame returnPayload jobs tagged rest work returnRest next branching weight before after hvisit hreturn hwork hrest hexp htag happend hweight hbranch hbefore hafter
 let qs : Fin 3 → Program 4 := ![
   .composition OriginalHereditaryBudgetSum.jobBudget ![.projection 0,.projection 3],
   .composition OriginalHereditaryBudgetSum.sum ![.projection 1,.projection 3],
   .composition OriginalHereditaryAgendaPotential.agenda ![.projection 2,.projection 3] ]
 let xs : Fin 4 → OTerm alpha := Fin.cons parent (Fin.cons jobs (Fin.cons rest (Fin.cons branching Fin.elim0)))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hj hquery
 let xx : Fin 4 → OTerm beta := Fin.cons (parent.relabel j) (Fin.cons (jobs.relabel j) (Fin.cons (rest.relabel j) (Fin.cons (branching.relabel j) Fin.elim0)))
 have hx : (fun i => (xs i).relabel j) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 rw [hx] at hquery
 have hq := binaryRecover OriginalHereditaryBudgetSum.jobBudget (.projection 0) (.projection 3)
   (ys 0) (parent.relabel j) (branching.relabel j) xx (hquery 0) (projectionValue 0 xx) (projectionValue 3 xx)
 have hs := binaryRecover OriginalHereditaryBudgetSum.sum (.projection 1) (.projection 3)
   (ys 1) (jobs.relabel j) (branching.relabel j) xx (hquery 1) (projectionValue 1 xx) (projectionValue 3 xx)
 have hr := binaryRecover OriginalHereditaryAgendaPotential.agenda (.projection 2) (.projection 3)
   (ys 2) (rest.relabel j) (branching.relabel j) xx (hquery 2) (projectionValue 2 xx) (projectionValue 3 xx)
 have hvisit' := renameInto hvisit j Theta hj
 have hreturn' := renameInto hreturn j Theta hj
 have hwork' := renameInto hwork j Theta hj
 have hrest' := renameInto hrest j Theta hj
 have hexp' := renameInto hexp j Theta hj
 have htag' := renameInto htag j Theta hj
 have happend' := renameInto happend j Theta hj
 have hweight' := renameInto hweight j Theta hj
 have hbranch' := renameInto hbranch j Theta hj
 have hbefore' := renameInto hbefore j Theta hj
 have hafter' := renameInto hafter j Theta hj
 simp only [graph1Rename,graph2Rename,consGraphRename,orderRename,sucRelabel,zRelabel] at hvisit' hreturn' hwork' hrest' hexp' htag' happend' hweight' hbranch' hbefore' hafter'
 rw [orderRename]
 exact atValues body beta Theta
   (parent.relabel j) (visit.relabel j) (returnFrame.relabel j) (returnPayload.relabel j) (jobs.relabel j) (tagged.relabel j) (rest.relabel j) (work.relabel j) (returnRest.relabel j) (next.relabel j) (branching.relabel j) (weight.relabel j) (before.relabel j) (after.relabel j) (ys 0) (ys 1) (ys 2)
   hvisit' hreturn' hwork' hrest' hexp' htag' happend' hweight' hbranch' hbefore' hafter' hq hs hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialVisitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialVisitProof
