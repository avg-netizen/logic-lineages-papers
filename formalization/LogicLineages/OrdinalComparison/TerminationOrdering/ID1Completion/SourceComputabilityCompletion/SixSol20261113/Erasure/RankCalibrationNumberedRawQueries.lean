module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalCancellationNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedRawQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalCancellationNumberedProof (tupleSixRename)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCases (raw label head encoded args types extras : OTerm alpha) (psi : Formula alpha)
 (hc : Nonempty (Derivation body Delta (programGraph numberedConstructor raw ![label,head,encoded,args,types,extras])))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (p1 p2 p3 p4 p5 : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing (raw.relabel j) (numeral 5) p1)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing p1 (label.relabel j) p2)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing p2 (head.relabel j) p3)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing p3 (encoded.relabel j) p4)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing p4 (args.relabel j) p5)) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing p5 (types.relabel j) (extras.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let p5 : Program 6 := pairOf (.projection 4) (.projection 5)
 let p4 : Program 6 := pairOf (.projection 3) p5
 let p3 : Program 6 := pairOf (.projection 2) p4
 let p2 : Program 6 := pairOf (.projection 1) p3
 let p1 : Program 6 := pairOf (.projection 0) p2
 let qs : Fin 5 → Program 6 := ![p1,p2,p3,p4,p5]
 apply programsCases qs (![label,head,encoded,args,types,extras] : Fin 6 → OTerm alpha) psi
 intro beta j Theta ys hj hq
 simp only [tupleSixRename] at hq
 have hc' := renameInto hc j Theta hj
 simp only [programRename,tupleSixRename] at hc'
 let xs : Fin 6 → OTerm beta := ![label.relabel j,head.relabel j,encoded.relabel j,args.relabel j,types.relabel j,extras.relabel j]
 have h0 := binaryRecover InternalPairing.pairing (constant 6 5) p1
   (raw.relabel j) (numeral 5) (ys 0) xs hc' (constantValue 5 xs) (hq 0)
 have h1 := binaryRecover InternalPairing.pairing (.projection 0) p2
   (ys 0) (label.relabel j) (ys 1) xs (hq 0) (projectionValue 0 xs) (hq 1)
 have h2 := binaryRecover InternalPairing.pairing (.projection 1) p3
   (ys 1) (head.relabel j) (ys 2) xs (hq 1) (projectionValue 1 xs) (hq 2)
 have h3 := binaryRecover InternalPairing.pairing (.projection 2) p4
   (ys 2) (encoded.relabel j) (ys 3) xs (hq 2) (projectionValue 2 xs) (hq 3)
 have h4 := binaryRecover InternalPairing.pairing (.projection 3) p5
   (ys 3) (args.relabel j) (ys 4) xs (hq 3) (projectionValue 3 xs) (hq 4)
 have h5 := binaryRecover InternalPairing.pairing (.projection 4) (.projection 5)
   (ys 4) (types.relabel j) (extras.relabel j) xs (hq 4) (projectionValue 4 xs) (projectionValue 5 xs)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj h0 h1 h2 h3 h4 h5
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedRawQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.RankCalibrationNumberedRawQueries
