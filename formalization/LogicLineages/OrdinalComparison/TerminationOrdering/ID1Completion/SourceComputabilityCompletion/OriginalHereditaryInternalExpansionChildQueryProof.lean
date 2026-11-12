module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalListCodecSupportProof OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryExpansion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem childCases (input parameter : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta))
   (first second singleton : OTerm beta), (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 firstJob first (input.relabel rho) (parameter.relabel rho))) →
   Nonempty (Derivation body Theta (graph2 secondJob second (input.relabel rho) (parameter.relabel rho))) →
   Nonempty (Derivation body Theta (consGraph singleton second z)) →
   Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let single : Program 2 := .composition InternalListCodec.consCode ![secondJob,InternalAcceptance.constantZero 2]
 let qs : Fin 3 → Program 2 := ![firstJob,secondJob,single]
 let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel rho) (Fin.cons (parameter.relabel rho) Fin.elim0)
 have hx : (fun i => (xs i).relabel rho) = xx := by
   funext i
   exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
 rw [hx] at hq
 have hs := binaryRecover InternalListCodec.consCode secondJob (InternalAcceptance.constantZero 2)
   (ys 2) (ys 1) z xx (hq 2) (hq 1) (InternalRawListRecursionSupportProof.constantZero xx)
 exact next beta rho Theta (ys 0) (ys 1) (ys 2) hrho (hq 0) (hq 1) hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalExpansionChildQueryProof
