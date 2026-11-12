module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTypedArgumentExchange OriginalTypedArgumentExchangeRawProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem factsRename {beta : Type} (source target certificate : OTerm alpha) (v : Fin 14 → OTerm alpha) (rho : alpha → beta) :
 (facts source target certificate v).relabel rho = facts (source.relabel rho) (target.relabel rho) (certificate.relabel rho) (fun i => (v i).relabel rho) := by
 simp only [facts,conjunctionRename,graph2Rename,OriginalTypedArgumentObservationSwapSyntaxProof.geometryRename]

theorem rawCases (source target certificate : OTerm alpha) (psi : Formula alpha)
 (he : Nonempty (Derivation body Delta (graph3 edge (suc z) source target certificate)))
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (v : Fin 14 → OTerm beta),
  (∀ p ∈ Delta, p.relabel rho ∈ Theta) →
  Nonempty (Derivation body Theta (facts (source.relabel rho) (target.relabel rho) (certificate.relabel rho) v)) →
  Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons source (Fin.cons target (Fin.cons certificate Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries xs psi
 intro beta rho v Theta hrho hq
 have hv : (fun i => (xs i).relabel rho) = Fin.cons (source.relabel rho)
   (Fin.cons (target.relabel rho) (Fin.cons (certificate.relabel rho) Fin.elim0)) := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hv] at hq
 have he' := renameInto he rho Theta hrho
 simp only [graph3Rename,sucRelabel,zRelabel] at he'
 exact next beta rho Theta v hrho (atValues (source.relabel rho) (target.relabel rho) (certificate.relabel rho) v he' hq)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentExchangeRawCasesProof
