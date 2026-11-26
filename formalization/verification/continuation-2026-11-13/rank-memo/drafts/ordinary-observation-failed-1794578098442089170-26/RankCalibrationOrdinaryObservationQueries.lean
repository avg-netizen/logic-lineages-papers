module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryObservationQueries
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
theorem actualCases (R : Program 2) (H : Program 1)
 (head args parameter typ : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (headData headResult types headValue values sorted headAndBase data candidate payload c gamma : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph1 H headData (head.relabel j))) →
   Nonempty (Derivation body Theta (OriginalTypedDecoderStepSpecification.StepArrowFields headData headResult types)) →
   Nonempty (Derivation body Theta (graph1 OriginalHeadClassNumber.classNumber headValue (head.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalTypedArgumentObservations.argumentObservations
     (OriginalHereditaryEvaluatorDefinitions.evaluator R)) values (args.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph1 OriginalNumericListSort.sort sorted values)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing headAndBase headValue sorted)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing data (typ.relabel j) headAndBase)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing candidate (numeral 4) data)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing payload (head.relabel j) (args.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (parameter.relabel j) c gamma)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let hd : Program 4 := .composition H (fun _ : Fin 1 => .projection 0)
 let hv : Program 4 := .composition OriginalHeadClassNumber.classNumber (fun _ : Fin 1 => .projection 0)
 let vals : Program 4 := .composition (OriginalTypedArgumentObservations.argumentObservations
   (OriginalHereditaryEvaluatorDefinitions.evaluator R)) ![.projection 1,.projection 2]
 let sorted : Program 4 := .composition OriginalNumericListSort.sort (fun _ : Fin 1 => vals)
 let hab : Program 4 := pairOf hv sorted
 let dat : Program 4 := pairOf (.projection 3) hab
 let can : Program 4 := pairOf (constant 4 4) dat
 let pay : Program 4 := pairOf (.projection 0) (.projection 1)
 let qs : Fin 12 → Program 4 := ![hd,headOf hd,tailOf hd,hv,vals,sorted,hab,dat,can,pay,leftOf (.projection 2),rightOf (.projection 2)]
 apply programsCases qs (Fin.cons head (Fin.cons args (Fin.cons parameter (Fin.cons typ Fin.elim0)))) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 4 → OTerm beta := Fin.cons (head.relabel j) (Fin.cons (args.relabel j)
   (Fin.cons (parameter.relabel j) (Fin.cons (typ.relabel j) Fin.elim0)))
 have hh := unaryRecover H (.projection 0) (ys 0) (head.relabel j) xs (hq 0) (projectionValue 0 xs)
 have hf := OriginalTypedDecoderInternalScalarProof.arrowFields hd (ys 0) (ys 1) (ys 2) xs (hq 0) (hq 1) (hq 2)
 have hclass := unaryRecover OriginalHeadClassNumber.classNumber (.projection 0) (ys 3) (head.relabel j) xs (hq 3) (projectionValue 0 xs)
 have he := binaryRecover (OriginalTypedArgumentObservations.argumentObservations (OriginalHereditaryEvaluatorDefinitions.evaluator R))
   (.projection 1) (.projection 2) (ys 4) (args.relabel j) (parameter.relabel j) xs (hq 4) (projectionValue 1 xs) (projectionValue 2 xs)
 have hs := unaryRecover OriginalNumericListSort.sort vals (ys 5) (ys 4) xs (hq 5) (hq 4)
 have hpair := binaryRecover InternalPairing.pairing hv sorted (ys 6) (ys 3) (ys 5) xs (hq 6) (hq 3) (hq 5)
 have hdata := binaryRecover InternalPairing.pairing (.projection 3) hab (ys 7) (typ.relabel j) (ys 6) xs (hq 7) (projectionValue 3 xs) (hq 6)
 have hc := binaryRecover InternalPairing.pairing (constant 4 4) dat (ys 8) (numeral 4) (ys 7) xs (hq 8) (constantValue 4 xs) (hq 7)
 have hp := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) (ys 9) (head.relabel j) (args.relabel j) xs (hq 9) (projectionValue 0 xs) (projectionValue 1 xs)
 have hl := unaryRecover InternalUnpair.left (.projection 2) (ys 10) (parameter.relabel j) xs (hq 10) (projectionValue 2 xs)
 have hr := unaryRecover InternalUnpair.right (.projection 2) (ys 11) (parameter.relabel j) xs (hq 11) (projectionValue 2 xs)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10) (ys 11)
   hj hh hf hclass he hs hpair hdata hc hp (reconstructPair (parameter.relabel j) (ys 10) (ys 11) hl hr)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryObservationQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationOrdinaryObservationQueries
