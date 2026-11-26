module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem actual : ChildContentTargets.ArgumentsConsReturn := by
  intro Q body alpha Delta raw domain child0 child1 parameter jobs annotatedPrefix row first resultTail second returned hc he hp hm hr ht hret
  let p0 : Program 4 := pairOf (.projection 1) (.projection 2)
  let p1 : Program 4 := pairOf (.projection 0) p0
  let p2 : Program 4 := pairOf (.projection 1) (.projection 3)
  let p3 : Program 4 := pairOf (.projection 2) (.projection 3)
  let p4 : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 0) (.projection 0)
  let p5 : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 1) (OriginalRawSyntaxTransport.constant 4 0)
  let p6 : Program 4 := pairOf (.projection 0) p2
  let p7 : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 0) p3
  let p8 : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 0) p6
  let p9 : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 1) p7
  let p10 : Program 4 := pairOf (.projection 0) (.projection 1)
  let qs : Fin 11 → Program 4 := ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10]
  let xs : Fin 4 → OTerm alpha := ![domain,child0,child1,parameter]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph2Rename]
  let xx : Fin 4 → OTerm beta := ![domain.relabel j,child0.relabel j,child1.relabel j,parameter.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro i
          refine Fin.cases ?_ ?_ i
          · rfl
          · intro i
            exact Fin.elim0 i
  rw [hx] at hq
  have hc' := renameInto hc j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  have hr' := renameInto hr j Theta hj
  have ht' := renameInto ht j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hc' he' hp' hm' hr' ht' hret'
  have b0 := binaryRecover InternalPairing.pairing (.projection 1) (.projection 2)
    (ys 0) (child0.relabel j) (child1.relabel j) xx (hq 0) (projectionValue 1 xx) (projectionValue 2 xx)
  have b1 := binaryRecover InternalPairing.pairing (.projection 0) p0
    (ys 1) (domain.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have b2 := binaryRecover InternalPairing.pairing (.projection 1) (.projection 3)
    (ys 2) (child0.relabel j) (parameter.relabel j) xx (hq 2) (projectionValue 1 xx) (projectionValue 3 xx)
  have b3 := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 3) (child1.relabel j) (parameter.relabel j) xx (hq 3) (projectionValue 2 xx) (projectionValue 3 xx)
  have b4 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 0) (.projection 0)
    (ys 4) (numeral 0) (domain.relabel j) xx (hq 4) (constantValue 0 xx) (projectionValue 0 xx)
  have b5 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 1) (OriginalRawSyntaxTransport.constant 4 0)
    (ys 5) (numeral 1) (numeral 0) xx (hq 5) (constantValue 1 xx) (constantValue 0 xx)
  have b6 := binaryRecover InternalPairing.pairing (.projection 0) p2
    (ys 6) (domain.relabel j) (ys 2) xx (hq 6) (projectionValue 0 xx) (hq 2)
  have b7 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 0) p3
    (ys 7) (numeral 0) (ys 3) xx (hq 7) (constantValue 0 xx) (hq 3)
  have b8 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 0) p6
    (ys 8) (numeral 0) (ys 6) xx (hq 8) (constantValue 0 xx) (hq 6)
  have b9 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 1) p7
    (ys 9) (numeral 1) (ys 7) xx (hq 9) (constantValue 1 xx) (hq 7)
  have b10 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 10) (domain.relabel j) (child0.relabel j) xx (hq 10) (projectionValue 0 xx) (projectionValue 1 xx)
  have hraw := ChildConstructorPairProof.consPair (raw.relabel j) (domain.relabel j) (child0.relabel j) (child1.relabel j) (ys 0) (ys 1) hc' b0 b1
  exact ChildConsContentProof.atCoordinates Q (raw.relabel j) (domain.relabel j) (child0.relabel j) (child1.relabel j) (parameter.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (resultTail.relabel j) (second.relabel j) (returned.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10)
    hc' he' hp' hm' hr' ht' hret' b0 b1 hraw b2 b3 b4 b5 b6 b7 b8 b9 b10
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConsProof.actual
