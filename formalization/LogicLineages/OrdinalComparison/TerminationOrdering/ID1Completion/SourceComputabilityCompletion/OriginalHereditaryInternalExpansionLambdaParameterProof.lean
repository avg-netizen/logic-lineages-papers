module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionUnaryExtendedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaParameterProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (branchNumeralIntro)
open OriginalRawSyntaxTransportInternalConstructorFieldsProof (lambdaTag lambdaDomain)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem extensionCases (domain gamma window : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (extended childParameter : OTerm beta), (∀ p ∈ Delta, p.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode extended (domain.relabel rho) (gamma.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParameter (window.relabel rho) extended)) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let ext : Program 3 := .composition InternalListCodec.consCode ![.projection 0,.projection 1]
 let qs : Fin 2 → Program 3 := ![ext,pairOf (.projection 2) ext]
 let xs : Fin 3 → OTerm alpha := Fin.cons domain (Fin.cons gamma (Fin.cons window Fin.elim0))
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 3 → OTerm beta := Fin.cons (domain.relabel rho) (Fin.cons (gamma.relabel rho) (Fin.cons (window.relabel rho) Fin.elim0))
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
 rw [hx] at hq
 exact next beta rho Theta (ys 0) (ys 1) hrho
   (binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
     (ys 0) (domain.relabel rho) (gamma.relabel rho) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx))
   (binaryRecover InternalPairing.pairing (.projection 2) ext (ys 1) (window.relabel rho) (ys 0) xx
     (hq 1) (projectionValue 2 xx) (hq 0))

theorem parameterValue (input domain child parameter window gamma extended childParameter : OTerm alpha)
 (hctor : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor input domain child)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter window gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended domain gamma)))
 (hcp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParameter window extended))) :
 Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.firstParameter childParameter input parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 have hwindow : Nonempty (Derivation body Delta (programGraph (leftOf (.projection 1)) window xs)) :=
   unaryValue InternalUnpair.left (.projection 1) window parameter xs (pairLeft parameter window gamma hp) (projectionValue 1 xs)
 have hgamma : Nonempty (Derivation body Delta (programGraph (rightOf (.projection 1)) gamma xs)) :=
   unaryValue InternalUnpair.right (.projection 1) gamma parameter xs (pairRight parameter window gamma hp) (projectionValue 1 xs)
 have hdomain := lambdaDomain (.projection 0) input domain child xs (projectionValue 0 xs) hctor
 let ext : Program 2 := OriginalHereditaryExpansion.consOf (leftOf (rightOf (.projection 0))) (rightOf (.projection 1))
 have hext : Nonempty (Derivation body Delta (programGraph ext extended xs)) :=
   binaryValue InternalListCodec.consCode (leftOf (rightOf (.projection 0))) (rightOf (.projection 1))
     extended domain gamma xs he hdomain hgamma
 have hpair : Nonempty (Derivation body Delta (programGraph (pairOf (leftOf (.projection 1)) ext) childParameter xs)) :=
   binaryValue InternalPairing.pairing (leftOf (.projection 1)) ext childParameter window extended xs hcp hwindow hext
 apply branchNumeralIntro 1 1 (leftOf (.projection 0)) _ _ childParameter xs
   (lambdaTag (.projection 0) input domain child xs (projectionValue 0 xs) hctor)
 exact hpair
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaParameterProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionLambdaParameterProof
