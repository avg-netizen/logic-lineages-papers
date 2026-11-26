module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorComponentsQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCases (R : Program 2) (left right parameter : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (a ar b br row rowr inner out : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 (OriginalRootObservation.rootObservation R) a (left.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalRootObservation.rootObservation R) ar (right.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) b (left.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) br (right.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) row (left.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) rowr (right.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing inner b row)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing out a inner)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let q0 : Program 3 := .composition (OriginalRootObservation.rootObservation R) ![.projection 0,.projection 2]
 let q1 : Program 3 := .composition (OriginalRootObservation.rootObservation R) ![.projection 1,.projection 2]
 let q2 : Program 3 := .composition (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) ![.projection 0,.projection 2]
 let q3 : Program 3 := .composition (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) ![.projection 1,.projection 2]
 let q4 : Program 3 := .composition (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) ![.projection 0,.projection 2]
 let q5 : Program 3 := .composition (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) ![.projection 1,.projection 2]
 let inn : Program 3 := pairOf q2 q4
 let fin : Program 3 := pairOf q0 inn
 let qs : Fin 8 → Program 3 := ![q0,q1,q2,q3,q4,q5,inn,fin]
 apply programsCases qs (Fin.cons left (Fin.cons right (Fin.cons parameter Fin.elim0))) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xx : Fin 3 → OTerm beta := Fin.cons (left.relabel j) (Fin.cons (right.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))
 have h0 := binaryRecover (OriginalRootObservation.rootObservation R) (.projection 0) (.projection 2)
   (ys 0) (left.relabel j) (parameter.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 2 xx)
 have h1 := binaryRecover (OriginalRootObservation.rootObservation R) (.projection 1) (.projection 2)
   (ys 1) (right.relabel j) (parameter.relabel j) xx (hq 1) (projectionValue 1 xx) (projectionValue 2 xx)
 have h2 := binaryRecover (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) (.projection 0) (.projection 2)
   (ys 2) (left.relabel j) (parameter.relabel j) xx (hq 2) (projectionValue 0 xx) (projectionValue 2 xx)
 have h3 := binaryRecover (OriginalRootObservation.rootObservation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) (.projection 1) (.projection 2)
   (ys 3) (right.relabel j) (parameter.relabel j) xx (hq 3) (projectionValue 1 xx) (projectionValue 2 xx)
 have h4 := binaryRecover (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) (.projection 0) (.projection 2)
   (ys 4) (left.relabel j) (parameter.relabel j) xx (hq 4) (projectionValue 0 xx) (projectionValue 2 xx)
 have h5 := binaryRecover (OriginalHereditaryDeletionRows.rows (OriginalHereditaryEvaluatorDefinitions.evaluator R)) (.projection 1) (.projection 2)
   (ys 5) (right.relabel j) (parameter.relabel j) xx (hq 5) (projectionValue 1 xx) (projectionValue 2 xx)
 have h6 := binaryRecover InternalPairing.pairing q2 q4 (ys 6) (ys 2) (ys 4) xx (hq 6) (hq 2) (hq 4)
 have h7 := binaryRecover InternalPairing.pairing q0 inn (ys 7) (ys 0) (ys 6) xx (hq 7) (hq 0) (hq 6)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) hj h0 h1 h2 h3 h4 h5 h6 h7
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorComponentsQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorComponentsQueries
