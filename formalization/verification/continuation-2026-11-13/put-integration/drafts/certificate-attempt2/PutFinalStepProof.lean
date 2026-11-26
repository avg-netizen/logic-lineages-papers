module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutClosedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.GuardedErasureFinalGraphsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.SelectedNilProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutFinalStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc z)
open UniformCertificateCompletion PutIntegration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem targetType (s t label typ raw : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (hr : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ t)) := by
  let xs : Fin 2 → OTerm alpha := ![s,label]
  have ht := unaryValue InternalUnpair.left (.projection 0) typ s xs
    (pairLeft s typ raw hp) (projectionValue 0 xs)
  have h := OriginalRawSyntaxTransportInternalConstructorSupportProof.pathValue (PairPath.left (PairPath.here (leftOf (.projection 0 : Program 2))))
    (.projection 0) t typ xs (Fin.cons t Fin.elim0) hr (projectionValue 0 _) ht
  exact unaryRecover InternalUnpair.left (.projection 0) typ t (Fin.cons t Fin.elim0) h
    (projectionValue 0 _)

theorem step (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (s t cert parameter typ raw head base label : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P))
        (numeral 1) s parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor raw head base)))
    (hr : Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label)))
    (hc : Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label))) :
    Nonempty (Derivation body Delta
      (stepAccepted (finalData p H G W P) (finalInputs p H G W P).oldStep s t cert parameter)) := by
  let q := seed p H G W
  let M := InternalOriginalUniformContextMembership.contextMember p.base.member
  have hsource := iffForward
    (SixSol20261112.Integration.FinalErasureProof.finalSource q H G W P body alpha Delta
      (numeral 1) ![s,parameter]) hs
  have htarget := PutValidityPackedProof.packed H G M W s t parameter typ raw head base label
    hsource hp ho hr
  have hput := SixSol20261112.Erasure.PutRootInternalProof.introduction
    (OriginalUniverseDecoder.source H G M W) p.oldStep s t cert parameter typ raw head base label
    hsource hp ho hr hc
  have hmixed := PutCertificateProof.mixedLeaf H G M W q.oldStep s t cert parameter label hc hput
  have htag := PutWrapperGuardsProof.packedTag s typ raw head base hp ho
  have hclosed := PutClosedProof.closed (OriginalMixedLiteralEndpointDefinitions.endpoint H G M W)
    q.window (OriginalTransparentMixedDirectBottom.leaf H G M W q.oldStep) s t cert parameter htag hmixed
  have hleaf := SixSol20261112.Erasure.GuardedErasureFinalGraphsProof.leafToFinal q H G W P
    s t cert parameter hclosed
  have hselected := SixSol20261112.Erasure.SelectedNilProof.backward
    (InternalParameterizedStructuralEndpointGuard.selectedEndpoint (finalData p H G W P))
    (finalInputs p H G W P).oldStep (numeral 1) s t cert parameter
    (PutCertificateProof.pathNil s label cert hc) hleaf
  exact SixSol20261112.Erasure.GuardedErasureFinalGraphsProof.guardedOfCore q H G W P
    typ s t cert parameter hsource htarget (pairLeft s typ raw hp) (targetType s t label typ raw hp hr) hselected

theorem actualFinalPutStep : ActualFinalPutStep := by
  intro p H G W P body alpha Delta s t cert parameter typ raw head base label
  let A := Fields p H G W P s t cert parameter typ raw head base label
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨out⟩ := step p H G W P s t cert parameter typ raw head base label
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction out⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutFinalStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutFinalStepProof
