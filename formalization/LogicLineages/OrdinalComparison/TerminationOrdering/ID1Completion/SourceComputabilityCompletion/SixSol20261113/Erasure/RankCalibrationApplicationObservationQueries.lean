module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationCoordinatesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationObservationQueries
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
theorem actualCases (R : Program 2)
 (domain codomain fnType fnPacked argPacked parameter fnRaw argRaw : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (fv av fr ar fo ao observations typedData data candidate : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) fv (fnPacked.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph2 (OriginalHereditaryEvaluatorDefinitions.evaluator R) av (argPacked.relabel j) (parameter.relabel j))) →
   Nonempty (Derivation body Theta (graph1 variableRankRaw fr (fnRaw.relabel j))) →
   Nonempty (Derivation body Theta (graph1 variableRankRaw ar (argRaw.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing fo (fnType.relabel j) fv)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing ao (domain.relabel j) av)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing observations fo ao)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing typedData (codomain.relabel j) observations)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing data (domain.relabel j) typedData)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing candidate (numeral 2) data)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let ef : Program 8 := .composition (OriginalHereditaryEvaluatorDefinitions.evaluator R) ![.projection 3,.projection 5]
 let ea : Program 8 := .composition (OriginalHereditaryEvaluatorDefinitions.evaluator R) ![.projection 4,.projection 5]
 let rf : Program 8 := .composition variableRankRaw (fun _ : Fin 1 => .projection 6)
 let ra : Program 8 := .composition variableRankRaw (fun _ : Fin 1 => .projection 7)
 let ofn : Program 8 := pairOf (.projection 2) ef
 let oarg : Program 8 := pairOf (.projection 0) ea
 let obs : Program 8 := pairOf ofn oarg
 let td : Program 8 := pairOf (.projection 1) obs
 let dat : Program 8 := pairOf (.projection 0) td
 let can : Program 8 := pairOf (constant 8 2) dat
 let qs : Fin 10 → Program 8 := ![ef,ea,rf,ra,ofn,oarg,obs,td,dat,can]
 apply programsCases qs (Fin.cons domain (Fin.cons codomain (Fin.cons fnType (Fin.cons fnPacked (Fin.cons argPacked (Fin.cons parameter (Fin.cons fnRaw (Fin.cons argRaw (Fin.elim0))))))))) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 8 → OTerm beta := Fin.cons (domain.relabel j) (Fin.cons (codomain.relabel j) (Fin.cons (fnType.relabel j) (Fin.cons (fnPacked.relabel j) (Fin.cons (argPacked.relabel j) (Fin.cons (parameter.relabel j) (Fin.cons (fnRaw.relabel j) (Fin.cons (argRaw.relabel j) (Fin.elim0))))))))
 have h0 := binaryRecover (OriginalHereditaryEvaluatorDefinitions.evaluator R) (.projection 3) (.projection 5)
   (ys 0) (fnPacked.relabel j) (parameter.relabel j) xs (hq 0) (projectionValue 3 xs) (projectionValue 5 xs)
 have h1 := binaryRecover (OriginalHereditaryEvaluatorDefinitions.evaluator R) (.projection 4) (.projection 5)
   (ys 1) (argPacked.relabel j) (parameter.relabel j) xs (hq 1) (projectionValue 4 xs) (projectionValue 5 xs)
 have h2 := unaryRecover variableRankRaw (.projection 6) (ys 2) (fnRaw.relabel j) xs
   (hq 2) (projectionValue 6 xs)
 have h3 := unaryRecover variableRankRaw (.projection 7) (ys 3) (argRaw.relabel j) xs
   (hq 3) (projectionValue 7 xs)
 have h4 := binaryRecover InternalPairing.pairing (.projection 2) (ef)
   (ys 4) (fnType.relabel j) (ys 0) xs (hq 4) (projectionValue 2 xs) (hq 0)
 have h5 := binaryRecover InternalPairing.pairing (.projection 0) (ea)
   (ys 5) (domain.relabel j) (ys 1) xs (hq 5) (projectionValue 0 xs) (hq 1)
 have h6 := binaryRecover InternalPairing.pairing (ofn) (oarg)
   (ys 6) (ys 4) (ys 5) xs (hq 6) (hq 4) (hq 5)
 have h7 := binaryRecover InternalPairing.pairing (.projection 1) (obs)
   (ys 7) (codomain.relabel j) (ys 6) xs (hq 7) (projectionValue 1 xs) (hq 6)
 have h8 := binaryRecover InternalPairing.pairing (.projection 0) (td)
   (ys 8) (domain.relabel j) (ys 7) xs (hq 8) (projectionValue 0 xs) (hq 7)
 have h9 := binaryRecover InternalPairing.pairing (constant 8 2) (dat)
   (ys 9) (numeral 2) (ys 8) xs (hq 9) (constantValue 2 xs) (hq 8)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) hj h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationObservationQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationApplicationObservationQueries
