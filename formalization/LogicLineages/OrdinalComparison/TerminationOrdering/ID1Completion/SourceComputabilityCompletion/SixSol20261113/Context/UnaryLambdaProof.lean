module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryChildContentTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof
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

theorem actual : UnaryChildContentTargets.LambdaReturn := by
  intro Q body alpha Delta input typ raw domain child codomain parameter jobs annotatedPrefix row first second returned hi hcon htype he hp hm hr hret
  let p0 : Program 4 := pairOf (.projection 0) (.projection 1)
  let p1 : Program 4 := leftOf (.projection 3)
  let p2 : Program 4 := rightOf (.projection 3)
  let p3 : Program 4 := OriginalHereditaryExpansion.consOf (.projection 0) p2
  let p4 : Program 4 := pairOf p1 p3
  let p5 : Program 4 := pairOf (.projection 1) p4
  let p6 : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 0) (.projection 2)
  let p7 : Program 4 := pairOf (.projection 2) p5
  let p8 : Program 4 := pairOf (OriginalRawSyntaxTransport.constant 4 0) p7
  let p9 : Program 4 := pairOf (.projection 2) (.projection 1)
  let qs : Fin 10 → Program 4 := ![p0,p1,p2,p3,p4,p5,p6,p7,p8,p9]
  let xs : Fin 4 → OTerm alpha := ![domain,child,codomain,parameter]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph2Rename]
  let xx : Fin 4 → OTerm beta := ![domain.relabel j,child.relabel j,codomain.relabel j,parameter.relabel j]
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
  have hi' := renameInto hi j Theta hj
  have hcon' := renameInto hcon j Theta hj
  have htype' := renameInto htype j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  have hr' := renameInto hr j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hi' hcon' htype' he' hp' hm' hr' hret'
  have b0 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) (ys 0) (domain.relabel j) (child.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have b1 := unaryRecover InternalUnpair.left (.projection 3) (ys 1) (parameter.relabel j) xx (hq 1) (projectionValue 3 xx)
  have b2 := unaryRecover InternalUnpair.right (.projection 3) (ys 2) (parameter.relabel j) xx (hq 2) (projectionValue 3 xx)
  have b3 := binaryRecover InternalListCodec.consCode (.projection 0) p2 (ys 3) (domain.relabel j) (ys 2) xx (hq 3) (projectionValue 0 xx) (hq 2)
  have b4 := binaryRecover InternalPairing.pairing p1 p3 (ys 4) (ys 1) (ys 3) xx (hq 4) (hq 1) (hq 3)
  have b5 := binaryRecover InternalPairing.pairing (.projection 1) p4 (ys 5) (child.relabel j) (ys 4) xx (hq 5) (projectionValue 1 xx) (hq 4)
  have b6 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 0) (.projection 2) (ys 6) (numeral 0) (codomain.relabel j) xx (hq 6) (constantValue 0 xx) (projectionValue 2 xx)
  have b7 := binaryRecover InternalPairing.pairing (.projection 2) p5 (ys 7) (codomain.relabel j) (ys 5) xx (hq 7) (projectionValue 2 xx) (hq 5)
  have b8 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 4 0) p7 (ys 8) (numeral 0) (ys 7) xx (hq 8) (constantValue 0 xx) (hq 7)
  have b9 := binaryRecover InternalPairing.pairing (.projection 2) (.projection 1) (ys 9) (codomain.relabel j) (child.relabel j) xx (hq 9) (projectionValue 2 xx) (projectionValue 1 xx)
  have hparameter := reconstructPair (parameter.relabel j) (ys 1) (ys 2) b1 b2
  exact UnaryLambdaContentProof.atCoordinates Q (input.relabel j) (typ.relabel j) (raw.relabel j) (domain.relabel j) (child.relabel j) (codomain.relabel j) (parameter.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) (ys 0) (ys 5) (ys 6) (ys 7) (ys 8) (ys 9) (ys 1) (ys 2) (ys 3) (ys 4)
    hi' hcon' htype' he' hp' hm' hr' hret' b0 b5 b6 b7 b8 b9 hparameter b3 b4
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryLambdaProof.actual
