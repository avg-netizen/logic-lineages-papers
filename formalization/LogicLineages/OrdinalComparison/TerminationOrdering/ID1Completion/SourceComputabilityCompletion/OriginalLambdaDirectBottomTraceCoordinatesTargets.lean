module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceCoordinatesTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Only internally queried original child selectors. Exact prefix/strip and
live-state provenance retained. No child transport or broad ChildIH premise. -/
def ActualChildCoordinates : Prop := ∀ (source : Program 2) (leaf : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t cert parameter next : OTerm alpha) (psi : Formula alpha),
 Nonempty (Derivation body Delta (graph4 (OriginalLambdaDirectBottomTrace.hop source leaf) (suc z) s t cert parameter)) →
 Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.childLive next s t cert parameter)) →
 (∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
 (childS childT childCert childParam : OTerm beta),
 (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
 Nonempty (Derivation body Theta (graph4 OriginalLambdaGuardLeaf.sourceBody childS (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho))) →
 Nonempty (Derivation body Theta (graph4 OriginalLambdaGuardLeaf.targetBody childT (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho))) →
 Nonempty (Derivation body Theta (graph4 OriginalLambdaGuardLeaf.childCertificate childCert (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho))) →
 Nonempty (Derivation body Theta (graph4 OriginalLambdaGuardLeaf.childParameter childParam (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho))) →
 Nonempty (Derivation body Theta (graph1 OriginalHereditaryLambda.prefixCertificate (cert.relabel rho) childCert)) →
 Nonempty (Derivation body Theta (graph1 OriginalLambdaGuardLeaf.stripCertificate childCert (cert.relabel rho))) →
 Nonempty (Derivation body Theta (graph4 OriginalHereditaryLambda.live (next.relabel rho) childS childT childCert childParam)) →
 Nonempty (Derivation body Theta (psi.relabel rho))) →
 Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceCoordinatesTargets
