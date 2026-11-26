module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalApplicationOrderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOrderProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaConstructorGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof InternalAcceptanceSupportProof
open InternalOriginalPairingOrderProof InternalOriginalApplicationOrderProof
open InternalOriginalOrderSyntaxProof
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalParameterizedBoundedDescentNormalizer (atMost)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The actual nested original lambda pairing is monotone in its body payload
at fixed domain/codomain. The common arrow is obtained by internal totality. -/
theorem packedLambdaBound (d e payload payload' parent parent' : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.packedLambda parent d e payload)))
    (hp' : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.packedLambda parent' d e payload')))
    (hb : Nonempty (Derivation body Delta (atMost payload' payload))) :
    Nonempty (Derivation body Delta (atMost parent' parent)) := by
  let ar : Program 4 := consOf (.projection 0) (.projection 1)
  let inner : Program 4 := pairOf (.projection 0) (.projection 2)
  let inner' : Program 4 := pairOf (.projection 0) (.projection 3)
  let node : Program 4 := pairOf (InternalLessThan.constantOne 4) inner
  let node' : Program 4 := pairOf (InternalLessThan.constantOne 4) inner'
  let qs : Fin 5 → Program 4 := ![ar,inner,inner',node,node']
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons payload (Fin.cons payload' Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [InternalParameterizedBoundedDescentNormalizerSyntaxProof.atMostRename]
  have hp1 := renameInto hp j Theta hj
  have hp2 := renameInto hp' j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [graph3Rename] at hp1 hp2
  simp only [InternalParameterizedBoundedDescentNormalizerSyntaxProof.atMostRename] at hb'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (payload.relabel j) (Fin.cons (payload'.relabel j) Fin.elim0)))
  have ha := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 0) (d.relabel j) (e.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have hi := binaryRecover InternalPairing.pairing (.projection 0) (.projection 2)
    (ys 1) (d.relabel j) (payload.relabel j) xx (hq 1) (projectionValue 0 xx) (projectionValue 2 xx)
  have hi' := binaryRecover InternalPairing.pairing (.projection 0) (.projection 3)
    (ys 2) (d.relabel j) (payload'.relabel j) xx (hq 2) (projectionValue 0 xx) (projectionValue 3 xx)
  have hn := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 4) inner
    (ys 3) (numeral 1) (ys 1) xx (hq 3) (InternalLessThanSupportProof.oneConstantValue xx) (hq 1)
  have hn' := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 4) inner'
    (ys 4) (numeral 1) (ys 2) xx (hq 4) (InternalLessThanSupportProof.oneConstantValue xx) (hq 2)
  have ho := packedOuter (parent.relabel j) (d.relabel j) (e.relabel j) (payload.relabel j)
    (ys 0) (ys 1) (ys 3) ha hi hn hp1
  have ho' := packedOuter (parent'.relabel j) (d.relabel j) (e.relabel j) (payload'.relabel j)
    (ys 0) (ys 2) (ys 4) ha hi' hn' hp2
  exact rightWeak (ys 0) (ys 4) (ys 3) (parent'.relabel j) (parent.relabel j) ho' ho
    (rightWeak (numeral 1) (ys 2) (ys 1) (ys 4) (ys 3) hn' hn
      (rightWeak (d.relabel j) (payload'.relabel j) (payload.relabel j) (ys 2) (ys 1) hi' hi hb'))

/-- Weak decrease of equal-typed bodies reflects to their actual right fields,
then propagates through the original constructor. All payloads are internal. -/
theorem lambdaBound (d e child child' parent parent' : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left e child)))
    (ht' : Nonempty (Derivation body Delta (graph1 InternalUnpair.left e child')))
    (hp : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor parent d e child)))
    (hp' : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor parent' d e child')))
    (hb : Nonempty (Derivation body Delta (atMost child' child))) :
    Nonempty (Derivation body Delta (atMost parent' parent)) := by
  let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1)]
  let xs : Fin 2 → OTerm alpha := Fin.cons child (Fin.cons child' Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [InternalParameterizedBoundedDescentNormalizerSyntaxProof.atMostRename]
  have ht1 := renameInto ht j Theta hj
  have ht2 := renameInto ht' j Theta hj
  have hp1 := renameInto hp j Theta hj
  have hp2 := renameInto hp' j Theta hj
  have hb' := renameInto hb j Theta hj
  rw [graph1Rename] at ht1 ht2
  rw [graph3Rename] at hp1 hp2
  simp only [InternalParameterizedBoundedDescentNormalizerSyntaxProof.atMostRename] at hb'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm beta := Fin.cons (child.relabel j) (Fin.cons (child'.relabel j) Fin.elim0)
  have hc := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (child.relabel j) xx
    (hq 0) (projectionValue 0 xx)
  have hc' := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (child'.relabel j) xx
    (hq 1) (projectionValue 1 xx)
  exact packedLambdaBound (d.relabel j) (e.relabel j) (ys 0) (ys 1)
    (parent.relabel j) (parent'.relabel j)
    (constructorForward (parent.relabel j) (d.relabel j) (e.relabel j) (child.relabel j) (ys 0) hc hp1)
    (constructorForward (parent'.relabel j) (d.relabel j) (e.relabel j) (child'.relabel j) (ys 1) hc' hp2)
    (payloadBound (e.relabel j) (child'.relabel j) (child.relabel j) (ys 1) (ys 0)
      ht2 ht1 hc' hc hb')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOrderProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalLambdaOrderProof
