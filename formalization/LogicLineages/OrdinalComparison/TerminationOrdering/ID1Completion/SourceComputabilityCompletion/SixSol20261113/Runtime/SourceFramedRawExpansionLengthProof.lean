module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NarrowCountRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedDeletionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRawExpansionLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem rawLength (input parameter window gamma children count jobs : OTerm alpha)
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children input)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (hl : Nonempty (Derivation body Delta (lengthGraph count gamma)))
 (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion jobs input parameter))) :
 Nonempty (Derivation body Delta (lengthGraph (add children count) jobs)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 apply programCompositionCases InternalApplicationValidityStackAppend.append
   ![OriginalHereditaryExpansion.childJobs,OriginalHereditaryExpansion.deletionJobs] jobs xs _ he
 intro beta rho ys Theta hrho happ hs
 simp only [lengthRename,InternalOriginalOrderSyntaxProof.addRelabel]
 let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hs
 have ht : Fin.cons (ys 0) (Fin.cons (ys 1) Fin.elim0) = ys := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 have happend : Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append (jobs.relabel rho) (ys 0) (ys 1))) := by
   simpa only [graph2,ht] using happ
 have ha' := renameInto ha rho Theta hrho
 have hp' := renameInto hp rho Theta hrho
 have hl' := renameInto hl rho Theta hrho
 simp only [graph1Rename,graph2Rename,lengthRename] at ha' hp' hl'
 have hdel := SourceFramedDeletionLengthProof.deletionLength
   (input.relabel rho) (parameter.relabel rho) (window.relabel rho) (gamma.relabel rho)
   (count.relabel rho) (ys 1) hp' hl' (hs 1)
 exact SixSol20261113.Context.NarrowCountRowsProof.rowsExact (input.relabel rho) (parameter.relabel rho) (ys 0) (ys 1)
   (jobs.relabel rho) (children.relabel rho) (count.relabel rho) (hs 0) happend ha' hdel
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRawExpansionLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRawExpansionLengthProof
