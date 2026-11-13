module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountRowsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalAdditionLawsProof (add)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
theorem actualRawExpansionLength : ScheduleCountTargets.ActualRawExpansionLength := by
 intro body alpha Delta raw parameter window gamma arity deletions jobs hp ha hl he
 let xs : Fin 2 → OTerm alpha := Fin.cons raw (Fin.cons parameter Fin.elim0)
 apply programCompositionCases InternalApplicationValidityStackAppend.append
   ![OriginalHereditaryExpansion.childJobs,OriginalHereditaryExpansion.deletionJobs] jobs xs _ he
 intro beta rho ys Theta hrho happ hs
 simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
 let xx : Fin 2 → OTerm beta := Fin.cons (raw.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hs
 have ht : Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have happend : Nonempty (Derivation body Theta
   (graph2 InternalApplicationValidityStackAppend.append (jobs.relabel rho) (ys 0) (ys 1))) := by
   simpa only [graph2,ht] using happ
 have hc : Nonempty (Derivation body Theta
   (graph2 OriginalHereditaryExpansion.childJobs (ys 0) (raw.relabel rho) (parameter.relabel rho))) := by
   simpa only [Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons] using hs 0
 have hd : Nonempty (Derivation body Theta
   (graph2 OriginalHereditaryExpansion.deletionJobs (ys 1) (raw.relabel rho) (parameter.relabel rho))) := by
   simpa only [Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons,graph2,xx] using hs 1
 have hp' := renameInto hp rho Theta hrho
 have ha' := renameInto ha rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 simp only [graph1Rename,graph2Rename,lengthRename] at hp' ha' hl'
 have hdeletion := OriginalHereditaryInternalExpansionLengthSupportProof.deletionLength
   (raw.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
   (deletions.relabel rho) (ys 1) hp' hl' hd
 exact ScheduleCountRowsProof.rowsExact (raw.relabel rho) (parameter.relabel rho) (ys 0) (ys 1)
   (jobs.relabel rho) (arity.relabel rho) (deletions.relabel rho) hc happend ha' hdeletion
theorem actualAnnotatedExpansionLength : ScheduleCountTargets.ActualAnnotatedExpansionLength := by
 intro body alpha Delta role typ raw parameter window gamma rawJob typed job arity deletions jobs
   hparam hraw htyped hjob harity hlength he
 let rawP : Program 1 := leftOf OriginalHereditaryAnnotatedExpansion.originalJob
 let parameterP : Program 1 := rightOf OriginalHereditaryAnnotatedExpansion.originalJob
 let rawExpansionP : Program 1 := .composition OriginalHereditaryExpansion.expansion ![rawP,parameterP]
 let qs : Fin 4 → Program 1 := ![leftOf (.projection 0),leftOf (rightOf (.projection 0)),rawP,rawExpansionP]
 let xs : Fin 1 → OTerm alpha := Fin.cons job Fin.elim0
 apply programCompositionCases OriginalHereditaryAnnotatedExpansion.decorateAll qs jobs xs _ he
 intro beta rho ys Theta hrho hdec hs
 simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
 let xx : Fin 1 → OTerm beta := Fin.cons (job.relabel rho) Fin.elim0
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hs
 have hp' := renameInto hparam rho Theta hrho
 have hr' := renameInto hraw rho Theta hrho
 have ht' := renameInto htyped rho Theta hrho
 have hj' := renameInto hjob rho Theta hrho
 have ha' := renameInto harity rho Theta hrho
 have hl' := renameInto hlength rho Theta hrho
 simp only [graph1Rename,graph2Rename,lengthRename] at hp' hr' ht' hj' ha' hl'
 have htypedSelector := unaryValue InternalUnpair.right (.projection 0) (typed.relabel rho) (job.relabel rho) xx
   (pairRight (job.relabel rho) (role.relabel rho) (typed.relabel rho) hj') (projectionValue 0 xx)
 have hrawJobSelector := unaryValue InternalUnpair.right (rightOf (.projection 0))
   (rawJob.relabel rho) (typed.relabel rho) xx
   (pairRight (typed.relabel rho) (typ.relabel rho) (rawJob.relabel rho) ht') htypedSelector
 have hrawSelector := unaryValue InternalUnpair.left OriginalHereditaryAnnotatedExpansion.originalJob
   (raw.relabel rho) (rawJob.relabel rho) xx
   (pairLeft (rawJob.relabel rho) (raw.relabel rho) (parameter.relabel rho) hr') hrawJobSelector
 have hparameterSelector := unaryValue InternalUnpair.right OriginalHereditaryAnnotatedExpansion.originalJob
   (parameter.relabel rho) (rawJob.relabel rho) xx
   (pairRight (rawJob.relabel rho) (raw.relabel rho) (parameter.relabel rho) hr') hrawJobSelector
 have hrawExp : Nonempty (Derivation body Theta (programGraph rawExpansionP (ys 3) xx)) := by
   simpa only [qs,Matrix.cons_val_three,Matrix.head_cons,Matrix.tail_cons] using hs 3
 have hrawExpansion := binaryRecover OriginalHereditaryExpansion.expansion rawP parameterP
   (ys 3) (raw.relabel rho) (parameter.relabel rho) xx hrawExp hrawSelector hparameterSelector
 have hrawLength := actualRawExpansionLength body beta Theta (raw.relabel rho) (parameter.relabel rho)
   (window.relabel rho) (gamma.relabel rho) (arity.relabel rho) (deletions.relabel rho) (ys 3)
   hp' ha' hl' hrawExpansion
 have hys : Fin.cons (ys 0) (Fin.cons (ys 1) (Fin.cons (ys 2) (Fin.cons (ys 3) Fin.elim0))) = ys := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
 have hdecorate : Nonempty (Derivation body Theta
   (graph4 OriginalHereditaryAnnotatedExpansion.decorateAll (jobs.relabel rho) (ys 0) (ys 1) (ys 2) (ys 3))) := by
   simpa only [graph4,hys] using hdec
 exact OriginalHereditaryInternalExpansionLengthSupportProof.annotationLength
   (ys 0) (ys 1) (ys 2) (ys 3) (jobs.relabel rho) (add (arity.relabel rho) (deletions.relabel rho))
   hdecorate hrawLength
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.ScheduleCountProof
