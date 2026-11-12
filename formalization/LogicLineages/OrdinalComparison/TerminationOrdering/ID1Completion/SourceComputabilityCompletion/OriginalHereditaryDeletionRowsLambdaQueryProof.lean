module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaCellProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases andIntro andLeft andRight)
open InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (fieldsRename)
open OriginalLambdaTraversalInternalFieldsSyntaxProof (lambdaFieldsRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalTagArithmeticSyntaxProof (suc)
theorem coordinateCases (Q : Program 2) (cutoff gamma c domain input other child otherChild parameter : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (rho : alpha → beta) (Theta : List (Formula beta)) (erasedType deleted deletedParam childDeleted childDeletedParam inputE otherE childE otherChildE value otherValue : OTerm beta),
 (∀ f ∈ Delta, f.relabel rho ∈ Theta) →
 Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup erasedType (cutoff.relabel rho) (gamma.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted (cutoff.relabel rho) (gamma.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing deletedParam (c.relabel rho) deleted)) →
 Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode childDeleted (domain.relabel rho) deleted)) →
 Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childDeletedParam (c.relabel rho) childDeleted)) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw inputE erasedType (cutoff.relabel rho) (input.relabel rho))) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw otherE erasedType (cutoff.relabel rho) (other.relabel rho))) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw childE erasedType (suc (cutoff.relabel rho)) (child.relabel rho))) →
 Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw otherChildE erasedType (suc (cutoff.relabel rho)) (otherChild.relabel rho))) →
 Nonempty (Derivation body Theta (graph2 Q value childE childDeletedParam)) →
 Nonempty (Derivation body Theta (graph2 Q otherValue otherChildE childDeletedParam)) →
 Nonempty (Derivation body Theta (psi.relabel rho))) :
 Nonempty (Derivation body Delta psi) := by
 let k : Program 9 := .composition .succ (fun _ : Fin 1 => .projection 0)
 let q0 : Program 9 := .composition InternalRawListRecursion.lookup ![.projection 0,.projection 1]
 let q1 : Program 9 := .composition OriginalClassContextAllPositionObserver.deleteAt ![.projection 0,.projection 1]
 let q2 : Program 9 := .composition InternalPairing.pairing ![.projection 2,q1]
 let q3 : Program 9 := .composition InternalListCodec.consCode ![.projection 3,q1]
 let q4 : Program 9 := .composition InternalPairing.pairing ![.projection 2,q3]
 let q5 : Program 9 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![q0,.projection 0,.projection 4]
 let q6 : Program 9 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![q0,.projection 0,.projection 5]
 let q7 : Program 9 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![q0,k,.projection 6]
 let q8 : Program 9 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![q0,k,.projection 7]
 let q9 : Program 9 := .composition Q ![q7,q4]
 let q10 : Program 9 := .composition Q ![q8,q4]
 let qs : Fin 11 → Program 9 := ![q0,q1,q2,q3,q4,q5,q6,q7,q8,q9,q10]
 let xs : Fin 9 → OTerm alpha := ![cutoff,gamma,c,domain,input,other,child,otherChild,parameter]
 apply queryCases qs xs psi
 intro beta rho ys Theta hrho hq
 let xx : Fin 9 → OTerm beta := ![cutoff.relabel rho,gamma.relabel rho,c.relabel rho,domain.relabel rho,input.relabel rho,other.relabel rho,child.relabel rho,otherChild.relabel rho,parameter.relabel rho]
 have he : (fun i => (xs i).relabel rho) = xx := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl ((fun k => Fin.elim0 k)))))))))) i
 rw [he] at hq
 have hk : Nonempty (Derivation body Theta (programGraph k (suc (cutoff.relabel rho)) xx)) :=
  unaryValue .succ (.projection 0) (suc (cutoff.relabel rho)) (cutoff.relabel rho) xx (successorValue (Fin.cons (cutoff.relabel rho) Fin.elim0)) (projectionValue 0 xx)
 have h0 := binaryRecover InternalRawListRecursion.lookup (.projection 0) (.projection 1) (ys 0) (cutoff.relabel rho) (gamma.relabel rho) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
 have h1 := binaryRecover OriginalClassContextAllPositionObserver.deleteAt (.projection 0) (.projection 1) (ys 1) (cutoff.relabel rho) (gamma.relabel rho) xx (hq 1) (projectionValue 0 xx) (projectionValue 1 xx)
 have h2 := binaryRecover InternalPairing.pairing (.projection 2) (q1) (ys 2) (c.relabel rho) (ys 1) xx (hq 2) (projectionValue 2 xx) (hq 1)
 have h3 := binaryRecover InternalListCodec.consCode (.projection 3) (q1) (ys 3) (domain.relabel rho) (ys 1) xx (hq 3) (projectionValue 3 xx) (hq 1)
 have h4 := binaryRecover InternalPairing.pairing (.projection 2) (q3) (ys 4) (c.relabel rho) (ys 3) xx (hq 4) (projectionValue 2 xx) (hq 3)
 have h5 := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (q0) (.projection 0) (.projection 4) (ys 5) (ys 0) (cutoff.relabel rho) (input.relabel rho) xx (hq 5) (hq 0) (projectionValue 0 xx) (projectionValue 4 xx)
 have h6 := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (q0) (.projection 0) (.projection 5) (ys 6) (ys 0) (cutoff.relabel rho) (other.relabel rho) xx (hq 6) (hq 0) (projectionValue 0 xx) (projectionValue 5 xx)
 have h7 := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (q0) (k) (.projection 6) (ys 7) (ys 0) (suc (cutoff.relabel rho)) (child.relabel rho) xx (hq 7) (hq 0) hk (projectionValue 6 xx)
 have h8 := InternalOriginalUniformVertexPathSupportProof.ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (q0) (k) (.projection 7) (ys 8) (ys 0) (suc (cutoff.relabel rho)) (otherChild.relabel rho) xx (hq 8) (hq 0) hk (projectionValue 7 xx)
 have h9 := binaryRecover Q (q7) (q4) (ys 9) (ys 7) (ys 4) xx (hq 9) (hq 7) (hq 4)
 have h10 := binaryRecover Q (q8) (q4) (ys 10) (ys 8) (ys 4) xx (hq 10) (hq 8) (hq 4)
 exact next beta rho Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10) hrho h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLambdaQueryProof
