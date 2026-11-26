module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
open FirstOrder Language
open InternalGraphComposition (OTerm)
theorem unaryVectorRename {alpha beta : Type} (x : OTerm alpha) (rho : alpha → beta) :
 (fun i : Fin 1 => ((![x] : Fin 1 → OTerm alpha) i).relabel rho) =
 (![x.relabel rho] : Fin 1 → OTerm beta) := by
 funext i
 exact Fin.cases (by simp only [Matrix.cons_val_zero]) (fun k => Fin.elim0 k) i

theorem binaryVectorRename {alpha beta : Type} (x y : OTerm alpha) (rho : alpha → beta) :
 (fun i : Fin 2 => ((![x,y] : Fin 2 → OTerm alpha) i).relabel rho) =
 (![x.relabel rho,y.relabel rho] : Fin 2 → OTerm beta) := by
 funext i
 exact Fin.cases (by simp only [Matrix.cons_val_zero])
   (Fin.cases (by simp only [Matrix.cons_val_succ,Matrix.cons_val_zero]) (fun k => Fin.elim0 k)) i
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsReverseInternalQuerySyntaxProof
