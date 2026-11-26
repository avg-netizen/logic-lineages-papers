module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaObservationQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual internal child computation and the entire original lambda observation
encoding are queried, not supplied as an interpretation premise. -/
theorem actualCases (R : Program 2) (packed parameter codomain domain : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (value observed typedData data candidate : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R)
     value (packed.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing observed (codomain.relabel j) value)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing typedData (codomain.relabel j) observed)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing data (domain.relabel j) typedData)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing candidate (numeral 1) data)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let ev : Program 4 := .composition (OriginalHereditaryEvaluatorDefinitions.evaluator R) ![.projection 0,.projection 1]
 let obs : Program 4 := pairOf (.projection 2) ev
 let td : Program 4 := pairOf (.projection 2) obs
 let dat : Program 4 := pairOf (.projection 3) td
 let can : Program 4 := pairOf (constant 4 1) dat
 let qs : Fin 5 → Program 4 := ![ev,obs,td,dat,can]
 apply programsCases qs (Fin.cons packed (Fin.cons parameter (Fin.cons codomain (Fin.cons domain Fin.elim0)))) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 4 → OTerm beta := Fin.cons (packed.relabel j) (Fin.cons (parameter.relabel j)
   (Fin.cons (codomain.relabel j) (Fin.cons (domain.relabel j) Fin.elim0)))
 have hv := binaryRecover (OriginalHereditaryEvaluatorDefinitions.evaluator R) (.projection 0) (.projection 1)
   (ys 0) (packed.relabel j) (parameter.relabel j) xs (hq 0) (projectionValue 0 xs) (projectionValue 1 xs)
 have ho := binaryRecover InternalPairing.pairing (.projection 2) ev
   (ys 1) (codomain.relabel j) (ys 0) xs (hq 1) (projectionValue 2 xs) (hq 0)
 have ht := binaryRecover InternalPairing.pairing (.projection 2) obs
   (ys 2) (codomain.relabel j) (ys 1) xs (hq 2) (projectionValue 2 xs) (hq 1)
 have hd := binaryRecover InternalPairing.pairing (.projection 3) td
   (ys 3) (domain.relabel j) (ys 2) xs (hq 3) (projectionValue 3 xs) (hq 2)
 have hc := binaryRecover InternalPairing.pairing (constant 4 1) dat
   (ys 4) (numeral 1) (ys 3) xs (hq 4) (constantValue 1 xs) (hq 3)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj hv ho ht hd hc
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaObservationQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationLambdaObservationQueries
