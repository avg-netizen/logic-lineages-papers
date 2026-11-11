module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawVariableRankSupportProof
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalFinalGuardedRankObserverProof OriginalFinalGuardedRankSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Rank of the actual packed application, with both real child ranks. -/
theorem applicationValue (out d e fn arg firstRank secondRank rank : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph4 application out d e fn arg)))
    (hf : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw firstRank fn)))
    (ha : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw secondRank arg)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalArithmeticPrograms.addition rank firstRank secondRank))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank out)) := by
  let f : Program 4 := rightOf (.projection 2)
  let a : Program 4 := rightOf (.projection 3)
  let children : Program 4 := pairOf f a
  let inner : Program 4 := pairOf (.projection 0) children
  let node : Program 4 := pairOf (two 4) inner
  let qs : Fin 5 → Program 4 := ![f,a,children,inner,node]
  let xs : Fin 4 → OTerm alpha := ![d,e,fn,arg]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have hc' := renameInto hc j Theta hj
  have hf' := renameInto hf j Theta hj
  have ha' := renameInto ha j Theta hj
  have hs' := renameInto hs j Theta hj
  rw [graph4Rename] at hc'
  rw [graph1Rename] at hf' ha'
  rw [graph2Rename] at hs'
  let xx : Fin 4 → OTerm beta := ![d.relabel j,e.relabel j,fn.relabel j,arg.relabel j]
  have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
    intro i
    simpa only [xs,xx,consTermRename,emptyRename] using hq i
  have hfr := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (fn.relabel j) xx
    (hq' 0) (projectionValue 2 xx)
  have har := unaryRecover InternalUnpair.right (.projection 3) (ys 1) (arg.relabel j) xx
    (hq' 1) (projectionValue 3 xx)
  have hchildren := binaryRecover InternalPairing.pairing f a (ys 2) (ys 0) (ys 1) xx
    (hq' 2) (hq' 0) (hq' 1)
  have hinner := binaryRecover InternalPairing.pairing (.projection 0) children (ys 3) (d.relabel j) (ys 2) xx
    (hq' 3) (projectionValue 0 xx) (hq' 2)
  have hnode := binaryRecover InternalPairing.pairing (two 4) inner (ys 4) (numeral 2) (ys 3) xx
    (hq' 4) (twoValue xx) (hq' 3)
  have hp := applicationForward (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j)
    (ys 0) (ys 1) (out.relabel j) hfr har hc'
  let px : Fin 4 → OTerm beta := ![d.relabel j,e.relabel j,ys 0,ys 1]
  have hcp := binaryValue InternalPairing.pairing (.projection 2) (.projection 3) (ys 2) (ys 0) (ys 1) px
    hchildren (projectionValue 2 px) (projectionValue 3 px)
  have hip := binaryValue InternalPairing.pairing (.projection 0) (pairOf (.projection 2) (.projection 3))
    (ys 3) (d.relabel j) (ys 2) px hinner (projectionValue 0 px) hcp
  have hnp := binaryValue InternalPairing.pairing (two 4)
    (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3)))
    (ys 4) (numeral 2) (ys 3) px hnode (twoValue px) hip
  have hout := binaryRecover InternalPairing.pairing (.projection 1)
    (pairOf (two 4) (pairOf (.projection 0) (pairOf (.projection 2) (.projection 3))))
    (out.relabel j) (e.relabel j) (ys 4) px hp (projectionValue 1 px) hnp
  let rx : Fin 3 → OTerm beta := ![d.relabel j,ys 0,ys 1]
  have hcr := binaryValue InternalPairing.pairing (.projection 1) (.projection 2)
    (ys 2) (ys 0) (ys 1) rx hchildren (projectionValue 1 rx) (projectionValue 2 rx)
  have hir := binaryValue InternalPairing.pairing (.projection 0) (pairOf (.projection 1) (.projection 2))
    (ys 3) (d.relabel j) (ys 2) rx hinner (projectionValue 0 rx) hcr
  have hraw : Nonempty (Derivation body Theta (graph3 applicationConstructor (ys 4) (d.relabel j) (ys 0) (ys 1))) :=
    binaryValue InternalPairing.pairing (constant 3 2) (pairOf (.projection 0) (pairOf (.projection 1) (.projection 2)))
      (ys 4) (numeral 2) (ys 3) rx hnode (constantValue 2 rx) hir
  have hrf := unaryRecover variableRankRaw InternalUnpair.right (firstRank.relabel j) (ys 0)
    (Fin.cons (fn.relabel j) Fin.elim0) hf' hfr
  have hra := unaryRecover variableRankRaw InternalUnpair.right (secondRank.relabel j) (ys 1)
    (Fin.cons (arg.relabel j) Fin.elim0) ha' har
  exact rankPackedBackward (out.relabel j) (rank.relabel j) (e.relabel j) (ys 4) hout
    (OriginalRawVariableRankApplicationProof.rankApplicationBackward (ys 4) (rank.relabel j)
      (d.relabel j) (ys 0) (ys 1) hraw
      (rankSumBackward (rank.relabel j) (ys 0) (ys 1) (firstRank.relabel j) (secondRank.relabel j) hrf hra hs'))

/-- Rank of the actual packed lambda is its body's rank. -/
theorem lambdaValue (out d e child rank : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor out d e child)))
    (hr : Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank child))) :
    Nonempty (Derivation body Delta (graph1 variableRankPackedRaw rank out)) := by
  let payload : Program 3 := rightOf (.projection 2)
  let inner : Program 3 := pairOf (.projection 0) payload
  let node : Program 3 := pairOf (InternalLessThan.constantOne 3) inner
  let arrow : Program 3 := consOf (.projection 0) (.projection 1)
  let qs : Fin 4 → Program 3 := ![payload,inner,node,arrow]
  let xs : Fin 3 → OTerm alpha := ![d,e,child]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have hc' := renameInto hc j Theta hj
  have hr' := renameInto hr j Theta hj
  rw [graph3Rename] at hc'
  rw [graph1Rename] at hr'
  let xx : Fin 3 → OTerm beta := ![d.relabel j,e.relabel j,child.relabel j]
  have hq' : ∀ i, Nonempty (Derivation body Theta (programGraph (qs i) (ys i) xx)) := by
    intro i
    simpa only [xs,xx,consTermRename,emptyRename] using hq i
  have hp := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (child.relabel j) xx
    (hq' 0) (projectionValue 2 xx)
  have hi := binaryRecover InternalPairing.pairing (.projection 0) payload
    (ys 1) (d.relabel j) (ys 0) xx (hq' 1) (projectionValue 0 xx) (hq' 0)
  have hn := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 3) inner
    (ys 2) (numeral 1) (ys 1) xx (hq' 2)
    (InternalLessThanSupportProof.oneConstantValue xx) (hq' 1)
  have ha := binaryRecover InternalListCodec.consCode (.projection 0) (.projection 1)
    (ys 3) (d.relabel j) (e.relabel j) xx (hq' 3) (projectionValue 0 xx) (projectionValue 1 xx)
  have hpacked := OriginalLambdaConstructorGraphSyntaxProof.constructorForward (out.relabel j)
    (d.relabel j) (e.relabel j) (child.relabel j) (ys 0) hp hc'
  have hout := OriginalLambdaConstructorGraphSupportProof.packedOuter (out.relabel j)
    (d.relabel j) (e.relabel j) (ys 0) (ys 3) (ys 1) (ys 2) ha hi hn hpacked
  let rx : Fin 2 → OTerm beta := ![d.relabel j,ys 0]
  have hir := binaryValue InternalPairing.pairing (.projection 0) (.projection 1)
    (ys 1) (d.relabel j) (ys 0) rx hi (projectionValue 0 rx) (projectionValue 1 rx)
  have hraw : Nonempty (Derivation body Theta (graph2 lambdaConstructor (ys 2) (d.relabel j) (ys 0))) :=
    binaryValue InternalPairing.pairing (constant 2 1) (pairOf (.projection 0) (.projection 1))
      (ys 2) (numeral 1) (ys 1) rx hn (constantValue 1 rx) hir
  have hchild := unaryRecover variableRankRaw InternalUnpair.right (rank.relabel j) (ys 0)
    (Fin.cons (child.relabel j) Fin.elim0) hr' hp
  exact rankPackedBackward (out.relabel j) (rank.relabel j) (ys 3) (ys 2) hout
    (OriginalRawVariableRankUnaryProof.rankLambdaBackward (ys 2) (rank.relabel j) (d.relabel j) (ys 0) hraw hchild)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankConstructorProof
