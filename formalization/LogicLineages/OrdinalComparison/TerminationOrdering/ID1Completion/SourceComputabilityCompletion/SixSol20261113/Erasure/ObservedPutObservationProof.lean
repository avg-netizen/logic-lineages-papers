module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutObservationSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionBelowSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutObservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion ObservedPut
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
attribute [local irreducible] programGraph

theorem actualFinalErasedObservations : ActualFinalErasedObservations := by
  intro p H G W P body alpha Delta input out typ parameter newParam context extended gamma d cutoff erasedInput erasedOut keyValue rank
  let A := (OriginalFunctionNeutrality.windowGraph (finalInputs p H G W P).window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises (finalData p H G W P) input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph (finalData p H G W P) out input parameter)) ⊓
    (OriginalIndexedObserverDefinitions.ActualRange cutoff parameter ⊓
    (graph2 InternalPairing.pairing parameter context extended ⊓
    (graph2 InternalPairing.pairing newParam context gamma ⊓
    (graph2 InternalRawListRecursion.lookup d cutoff extended ⊓
    (graph2 OriginalClassContextAllPositionObserver.deleteAt gamma cutoff extended ⊓
    (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedInput d cutoff input ⊓
      graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedOut d cutoff out))))))
  let B := ((graph2 (key p H G W) keyValue erasedInput newParam).iff
      (graph2 (key p H G W) keyValue erasedOut newParam)) ⊓
    ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedInput).iff
      (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank erasedOut))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have result : Nonempty (Derivation body (A :: Delta) B) := by
    let K := key p H G W
    let ki : Program 3 := .composition K ![.projection 0,.projection 2]
    let ko : Program 3 := .composition K ![.projection 1,.projection 2]
    let ri : Program 3 := .composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => .projection 0)
    let ro : Program 3 := .composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => .projection 1)
    let qs : Fin 5 → Program 3 := ![ki,ri,ko,ro,pairOf ki ri]
    let xs : Fin 3 → OTerm alpha := ![erasedInput,erasedOut,newParam]
    apply programsCases qs xs B
    intro beta j Theta ys hj hq
    simp only [B,conjunctionRename,OriginalContextInsertionBelowSyntaxProof.iffRename,graph1Rename,graph2Rename]
    have hh := renameInto h j Theta hj
    simp only [A,conjunctionRename,OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
      InternalParameterizedCanonicalResultFoldSyntaxProof.sourcePremisesRename,
      InternalParameterizedCanonicalResultFoldSyntaxProof.foldGraphRename,
      OriginalIndexedObserverRangeSyntaxProof.rangeRename,graph1Rename,graph2Rename,graph3Rename,
      InternalOriginalStepGuard.one,InternalTagArithmeticSyntaxProof.sucRelabel,InternalTagArithmeticSyntaxProof.zRelabel] at hh
    let xx : Fin 3 → OTerm beta := ![erasedInput.relabel j,erasedOut.relabel j,newParam.relabel j]
    have hxs : (fun i => (xs i).relabel j) = xx := by
      funext i
      exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
    rw [hxs] at hq
    have hki := binaryRecover K (.projection 0) (.projection 2) (ys 0)
      (erasedInput.relabel j) (newParam.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 2 xx)
    have hri := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (.projection 0)
      (ys 1) (erasedInput.relabel j) xx (hq 1) (projectionValue 0 xx)
    have hko := binaryRecover K (.projection 1) (.projection 2) (ys 2)
      (erasedOut.relabel j) (newParam.relabel j) xx (hq 2) (projectionValue 1 xx) (projectionValue 2 xx)
    have hro := unaryRecover OriginalRawSyntaxTransport.variableRankPackedRaw (.projection 1)
      (ys 3) (erasedOut.relabel j) xx (hq 3) (projectionValue 1 xx)
    have hm := binaryRecover InternalPairing.pairing ki ri (ys 4) (ys 0) (ys 1) xx (hq 4) (hq 0) (hq 1)
    exact ObservedPutObservationSupportProof.atValues p H G W P
      (input.relabel j) (out.relabel j) (typ.relabel j) (parameter.relabel j) (newParam.relabel j)
      (context.relabel j) (extended.relabel j) (gamma.relabel j) (d.relabel j) (cutoff.relabel j)
      (erasedInput.relabel j) (erasedOut.relabel j) (keyValue.relabel j) (rank.relabel j)
      (ys 0) (ys 1) (ys 2) (ys 3) (ys 4)
      (andLeft hh) (andLeft (andRight hh)) (andLeft (andRight (andRight hh)))
      (andLeft (andRight (andRight (andRight hh))))
      (andLeft (andRight (andRight (andRight (andRight hh)))))
      (andLeft (andRight (andRight (andRight (andRight (andRight hh))))))
      (andLeft (andRight (andRight (andRight (andRight (andRight (andRight hh)))))))
      (andRight (andRight (andRight (andRight (andRight (andRight (andRight hh)))))))
      hki hri hko hro hm
  exact ⟨Derivation.implicationIntroduction (Classical.choice result)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutObservationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ObservedPutObservationProof
