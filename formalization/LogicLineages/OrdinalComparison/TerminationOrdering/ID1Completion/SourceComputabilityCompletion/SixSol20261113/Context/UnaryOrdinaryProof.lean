module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryContentProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryChildContentTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof
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

theorem actual : UnaryChildContentTargets.OrdinaryReturn := by
  intro Q body alpha Delta input typ raw domain child parameter jobs annotatedPrefix row first second returned hi hcon he hp hm hr hret
  let p0 : Program 3 := pairOf (.projection 0) (.projection 1)
  let p1 : Program 3 := pairOf (.projection 1) (.projection 2)
  let p2 : Program 3 := pairOf (OriginalRawSyntaxTransport.constant 3 1) (OriginalRawSyntaxTransport.constant 3 0)
  let p3 : Program 3 := pairOf (OriginalRawSyntaxTransport.constant 3 0) p1
  let p4 : Program 3 := pairOf (OriginalRawSyntaxTransport.constant 3 1) p3
  let qs : Fin 5 → Program 3 := ![p0,p1,p2,p3,p4]
  let xs : Fin 3 → OTerm alpha := ![domain,child,parameter]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph2Rename]
  let xx : Fin 3 → OTerm beta := ![domain.relabel j,child.relabel j,parameter.relabel j]
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
          exact Fin.elim0 i
  rw [hx] at hq
  have hi' := renameInto hi j Theta hj
  have hcon' := renameInto hcon j Theta hj
  have he' := renameInto he j Theta hj
  have hp' := renameInto hp j Theta hj
  have hm' := renameInto hm j Theta hj
  have hr' := renameInto hr j Theta hj
  have hret' := renameInto hret j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,graph5Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename] at hi' hcon' he' hp' hm' hr' hret'
  have b0 := binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) (ys 0) (domain.relabel j) (child.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have b1 := binaryRecover InternalPairing.pairing (.projection 1) (.projection 2) (ys 1) (child.relabel j) (parameter.relabel j) xx (hq 1) (projectionValue 1 xx) (projectionValue 2 xx)
  have b2 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 1) (OriginalRawSyntaxTransport.constant 3 0) (ys 2) (numeral 1) (numeral 0) xx (hq 2) (constantValue 1 xx) (constantValue 0 xx)
  have b3 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 0) p1 (ys 3) (numeral 0) (ys 1) xx (hq 3) (constantValue 0 xx) (hq 1)
  have b4 := binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 1) p3 (ys 4) (numeral 1) (ys 3) xx (hq 4) (constantValue 1 xx) (hq 3)
  exact UnaryOrdinaryContentProof.atCoordinates Q (input.relabel j) (typ.relabel j) (raw.relabel j) (domain.relabel j) (child.relabel j) (parameter.relabel j) (jobs.relabel j) (annotatedPrefix.relabel j) (row.relabel j) (first.relabel j) (second.relabel j) (returned.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
    hi' hcon' he' hp' hm' hr' hret' b0 b1 b2 b3 b4
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.UnaryOrdinaryProof.actual
