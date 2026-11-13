module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedObservationQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport (constant variableRankRaw)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCases (R : Program 2) (H : Program 1)
 (label head args extras parameter typ : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (headData headResult types headValue values sorted extraValues baseRank extraRank baseAndExtras headAndArgs typedData data candidate c gamma : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 H headData (head.relabel j))) →
   Nonempty (Derivation body Theta (OriginalTypedDecoderStepSpecification.StepArrowFields headData headResult types)) →
   Nonempty (Derivation body Theta (graph1 OriginalHeadClassNumber.classNumber headValue (head.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalTypedArgumentObservations.argumentObservations
     (OriginalHereditaryEvaluatorDefinitions.evaluator R)) values (args.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph1 OriginalNumericListSort.sort sorted values)) →
   Nonempty (Derivation body Theta (graph2 (OriginalTypedArgumentObservations.argumentObservations
     (OriginalHereditaryEvaluatorDefinitions.evaluator R)) extraValues (extras.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph1 variableRankRaw baseRank (args.relabel j))) →
   Nonempty (Derivation body Theta (graph1 variableRankRaw extraRank (extras.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing baseAndExtras sorted extraValues)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing headAndArgs headValue baseAndExtras)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing typedData (typ.relabel j) headAndArgs)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing data (label.relabel j) typedData)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing candidate (numeral 5) data)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (parameter.relabel j) c gamma)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let hd : Program 6 := .composition H (fun _ : Fin 1 => .projection 1)
 let hv : Program 6 := .composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => .projection 1)
 let vals : Program 6 := .composition (OriginalTypedArgumentObservations.argumentObservations
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) ![.projection 2,.projection 4]
 let sorted : Program 6 := .composition OriginalNumericListSort.sort (fun _ : Fin 1 => vals)
 let ev : Program 6 := .composition (OriginalTypedArgumentObservations.argumentObservations
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) ![.projection 3,.projection 4]
 let br : Program 6 := .composition variableRankRaw (fun _ : Fin 1 => .projection 2)
 let er : Program 6 := .composition variableRankRaw (fun _ : Fin 1 => .projection 3)
 let bae : Program 6 := pairOf sorted ev
 let ha : Program 6 := pairOf hv bae
 let td : Program 6 := pairOf (.projection 5) ha
 let dat : Program 6 := pairOf (.projection 0) td
 let can : Program 6 := pairOf (constant 6 5) dat
 let qs : Fin 16 → Program 6 := ![hd,headOf hd,tailOf hd,hv,vals,sorted,ev,br,er,bae,ha,td,dat,can,leftOf (.projection 4),rightOf (.projection 4)]
 apply programsCases qs (Fin.cons label (Fin.cons head (Fin.cons args (Fin.cons extras (Fin.cons parameter (Fin.cons typ Fin.elim0)))))) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 6 → OTerm beta := Fin.cons (label.relabel j) (Fin.cons (head.relabel j) (Fin.cons (args.relabel j)
   (Fin.cons (extras.relabel j) (Fin.cons (parameter.relabel j) (Fin.cons (typ.relabel j) Fin.elim0)))))
 have hh := unaryRecover H (.projection 1) (ys 0) (head.relabel j) xs (hq 0) (projectionValue 1 xs)
 have hf := OriginalTypedDecoderInternalScalarProof.arrowFields hd (ys 0) (ys 1) (ys 2) xs (hq 0) (hq 1) (hq 2)
 have hclass := unaryRecover OriginalHeadClassNumber.classNumber (.projection 1) (ys 3) (head.relabel j) xs (hq 3) (projectionValue 1 xs)
 have hbv := binaryRecover (OriginalTypedArgumentObservations.argumentObservations (OriginalHereditaryEvaluatorDefinitions.evaluator R))
   (.projection 2) (.projection 4) (ys 4) (args.relabel j) (parameter.relabel j) xs (hq 4) (projectionValue 2 xs) (projectionValue 4 xs)
 have hs := unaryRecover OriginalNumericListSort.sort vals (ys 5) (ys 4) xs (hq 5) (hq 4)
 have hev := binaryRecover (OriginalTypedArgumentObservations.argumentObservations (OriginalHereditaryEvaluatorDefinitions.evaluator R))
   (.projection 3) (.projection 4) (ys 6) (extras.relabel j) (parameter.relabel j) xs (hq 6) (projectionValue 3 xs) (projectionValue 4 xs)
 have hbr := unaryRecover variableRankRaw (.projection 2) (ys 7) (args.relabel j) xs (hq 7) (projectionValue 2 xs)
 have her := unaryRecover variableRankRaw (.projection 3) (ys 8) (extras.relabel j) xs (hq 8) (projectionValue 3 xs)
 have hbae := binaryRecover InternalPairing.pairing sorted ev (ys 9) (ys 5) (ys 6) xs (hq 9) (hq 5) (hq 6)
 have hha := binaryRecover InternalPairing.pairing hv bae (ys 10) (ys 3) (ys 9) xs (hq 10) (hq 3) (hq 9)
 have htd := binaryRecover InternalPairing.pairing (.projection 5) ha (ys 11) (typ.relabel j) (ys 10) xs (hq 11) (projectionValue 5 xs) (hq 10)
 have hdat := binaryRecover InternalPairing.pairing (.projection 0) td (ys 12) (label.relabel j) (ys 11) xs (hq 12) (projectionValue 0 xs) (hq 11)
 have hcan := binaryRecover InternalPairing.pairing (constant 6 5) dat (ys 13) (numeral 5) (ys 12) xs (hq 13) (constantValue 5 xs) (hq 12)
 have hl := unaryRecover InternalUnpair.left (.projection 4) (ys 14) (parameter.relabel j) xs (hq 14) (projectionValue 4 xs)
 have hr := unaryRecover InternalUnpair.right (.projection 4) (ys 15) (parameter.relabel j) xs (hq 15) (projectionValue 4 xs)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10) (ys 11) (ys 12) (ys 13) (ys 14) (ys 15) hj
   hh hf hclass hbv hs hev hbr her hbae hha htd hdat hcan
   (reconstructPair (parameter.relabel j) (ys 14) (ys 15) hl hr)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedObservationQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedObservationQueries
