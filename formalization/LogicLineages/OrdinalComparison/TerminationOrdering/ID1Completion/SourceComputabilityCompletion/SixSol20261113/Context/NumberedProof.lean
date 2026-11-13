module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedChildContentTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof
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

theorem actual : NumberedChildContentTargets.NumberedReturn := by
  intro Q body alpha Delta input typ raw label head encodedType base extraTypes extras parameter jobs annotatedPrefix row first resultTail second returned hi hc he hp hm hr ht hret
  let p0 : Program 7 := pairOf (.projection 4) (.projection 5)
  let p1 : Program 7 := pairOf (.projection 3) p0
  let p2 : Program 7 := pairOf (.projection 2) p1
  let p3 : Program 7 := pairOf (.projection 1) p2
  let p4 : Program 7 := pairOf (.projection 0) p3
  let p5 : Program 7 := pairOf (.projection 3) (.projection 6)
  let p6 : Program 7 := pairOf (.projection 5) (.projection 6)
  let p7 : Program 7 := pairOf (OriginalRawSyntaxTransport.constant 7 1) (OriginalRawSyntaxTransport.constant 7 0)
  let p8 : Program 7 := pairOf (OriginalRawSyntaxTransport.constant 7 0) p5
  let p9 : Program 7 := pairOf (OriginalRawSyntaxTransport.constant 7 0) p6
  let p10 : Program 7 := pairOf (OriginalRawSyntaxTransport.constant 7 1) p8
  let p11 : Program 7 := pairOf (OriginalRawSyntaxTransport.constant 7 1) p9
  let qs : Fin 12 → Program 7 := ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9,p10,p11]
  let xs : Fin 7 → OTerm alpha := ![label,head,encodedType,base,extraTypes,extras,parameter]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph2Rename]
  let xx : Fin 7 → OTerm beta := ![label.relabel j,head.relabel j,encodedType.relabel j,base.relabel j,extraTypes.relabel j,extras.relabel j,parameter.relabel j]
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
  have hi' := renameInto hi j Theta hj
  have hc' := renameInto hc j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  have hr' := renameInto hr j Theta hj
  have ht' := renameInto ht j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hi' he' hp' hm' hr' ht' hret'
  simp only [programRename,consTermRename,emptyRename] at hc'
  have b0 := binaryRecover InternalPairing.pairing (.projection 4) (.projection 5) (ys 0) (extraTypes.relabel j) (extras.relabel j) xx (hq 0) (projectionValue 4 xx) (projectionValue 5 xx)
  have b1 := binaryRecover InternalPairing.pairing (.projection 3) p0 (ys 1) (base.relabel j) (ys 0) xx (hq 1) (projectionValue 3 xx) (hq 0)
  have b2 := binaryRecover InternalPairing.pairing (.projection 2) p1 (ys 2) (encodedType.relabel j) (ys 1) xx (hq 2) (projectionValue 2 xx) (hq 1)
  have b3 := binaryRecover InternalPairing.pairing (.projection 1) p2 (ys 3) (head.relabel j) (ys 2) xx (hq 3) (projectionValue 1 xx) (hq 2)
  have b4 := binaryRecover InternalPairing.pairing (.projection 0) p3 (ys 4) (label.relabel j) (ys 3) xx (hq 4) (projectionValue 0 xx) (hq 3)
  have b5 := binaryRecover InternalPairing.pairing (.projection 3) (.projection 6) (ys 5) (base.relabel j) (parameter.relabel j) xx (hq 5) (projectionValue 3 xx) (projectionValue 6 xx)
  have b6 := binaryRecover InternalPairing.pairing (.projection 5) (.projection 6) (ys 6) (extras.relabel j) (parameter.relabel j) xx (hq 6) (projectionValue 5 xx) (projectionValue 6 xx)
  have b7 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 7 1) (OriginalRawSyntaxTransport.constant 7 0) (ys 7) (numeral 1) (numeral 0) xx (hq 7) (constantValue 1 xx) (constantValue 0 xx)
  have b8 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 7 0) p5 (ys 8) (numeral 0) (ys 5) xx (hq 8) (constantValue 0 xx) (hq 5)
  have b9 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 7 0) p6 (ys 9) (numeral 0) (ys 6) xx (hq 9) (constantValue 0 xx) (hq 6)
  have b10 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 7 1) p8 (ys 10) (numeral 1) (ys 8) xx (hq 10) (constantValue 1 xx) (hq 8)
  have b11 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 7 1) p9 (ys 11) (numeral 1) (ys 9) xx (hq 11) (constantValue 1 xx) (hq 9)
  exact NumberedContentProof.atCoordinates Q (input.relabel j) (typ.relabel j) (raw.relabel j) (label.relabel j) (head.relabel j) (encodedType.relabel j) (base.relabel j) (extraTypes.relabel j) (extras.relabel j) (parameter.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (resultTail.relabel j) (second.relabel j) (returned.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 10) (ys 11)
    hi' hc' he' hp' hm' hr' ht' hret' b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.NumberedProof.actual
