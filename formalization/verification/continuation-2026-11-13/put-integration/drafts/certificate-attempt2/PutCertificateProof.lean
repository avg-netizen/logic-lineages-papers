module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PutRootInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalBooleanProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutWrapperGuardsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutCertificateProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceBranchProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open OriginalRawSyntaxTransportInternalConstructorSupportProof (numeralNeApply)
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def rootTag : Program 1 := leftOf (rightOf (rightOf (.projection 0)))

theorem pathNil (s label cert : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)) := by
  have h := OriginalRawSyntaxTransportInternalConstructorSupportProof.pathValue (PairPath.left (PairPath.here (OriginalRawSyntaxTransport.constant 2 0)))
    (.projection 0) cert z ![s,label] (Fin.cons cert Fin.elim0) hc
    (projectionValue 0 _) (constantValue 0 _)
  exact unaryRecover InternalUnpair.left (.projection 0) z cert (Fin.cons cert Fin.elim0) h
    (projectionValue 0 _)

theorem putRootTag (s label cert : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label))) :
    Nonempty (Derivation body Delta (graph1 rootTag z cert)) := by
  exact OriginalRawSyntaxTransportInternalConstructorSupportProof.pathValue (PairPath.right (PairPath.right
      (PairPath.left (PairPath.here (OriginalRawSyntaxTransport.constant 2 0)))))
    (.projection 0) cert z ![s,label] (Fin.cons cert Fin.elim0) hc
    (projectionValue 0 _) (constantValue 0 _)

theorem bottomRootTag (s cert : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (graph1 OriginalTransparentDirectBottom.certificateCode cert s))) :
    Nonempty (Derivation body Delta (graph1 rootTag (numeral 3) cert)) := by
  exact OriginalRawSyntaxTransportInternalConstructorSupportProof.pathValue (PairPath.right (PairPath.right
      (PairPath.left (PairPath.here (InternalFixedWindowVertexDispatch.constant 1 3)))))
    (.projection 0) cert (numeral 3) (Fin.cons s Fin.elim0) (Fin.cons cert Fin.elim0) hc
    (projectionValue 0 _) (InternalFixedWindowVertexDispatchSupportProof.constantValue 1 3 _)

theorem bottomInactive (s t cert parameter label : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label))) :
    Nonempty (Derivation body Delta (graph4 OriginalTransparentDirectBottom.active z s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
  let q : Program 4 := .composition OriginalTransparentDirectBottom.certificateCode
    (fun _ : Fin 1 => .projection 0)
  let A := graph4 OriginalTransparentDirectBottom.active (suc z) s t cert parameter
  have hn : Nonempty (Derivation body Delta A.not) := by
    have ha : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hq := OriginalTransparentLambdaValidityInternalBooleanProof.sameLeftRecover
      (.projection 2) q cert xs ha (projectionValue 2 xs)
    have hbottom := unaryRecover OriginalTransparentDirectBottom.certificateCode (.projection 0)
      cert s xs hq (projectionValue 0 xs)
    have h3 := bottomRootTag s cert hbottom
    have h0 := putRootTag s label cert (withHyp hc A)
    obtain ⟨he⟩ := valueUnique rootTag z (numeral 3) (Fin.cons cert Fin.elim0) h0 h3
    exact ⟨Derivation.implicationIntroduction (numeralNeApply 0 3 (by decide) he)⟩
  exact OriginalTransparentLambdaValidityInternalBooleanProof.sameReject (.projection 2) q xs hn

theorem mixedLeaf (H G : Program 1) (M W : Program 2) (leaf : Program 4)
    (s t cert parameter label : OTerm alpha)
    (hc : Nonempty (Derivation body Delta
      (graph2 SixSol20261112.Erasure.PutRoot.certificateCode cert s label)))
    (hl : Nonempty (Derivation body Delta (graph4 leaf (suc z) s t cert parameter))) :
    Nonempty (Derivation body Delta
      (graph4 (OriginalTransparentMixedDirectBottom.leaf H G M W leaf) (suc z) s t cert parameter)) := by
  have hb := zeroBranchIntro OriginalTransparentDirectBottom.active leaf
    (OriginalTransparentDirectBottom.acceptedValue (OriginalUniverseDecoder.source H G M W))
    (suc z) ![s,t,cert,parameter] (bottomInactive s t cert parameter label hc) hl
  exact OriginalTransparentMixedPathNilProof.introduction (OriginalUniverseDecoder.source H G M W)
    (OriginalTransparentDirectBottom.refined (OriginalUniverseDecoder.source H G M W) leaf)
    (suc z) s t cert parameter (pathNil s label cert hc) hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutCertificateProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutCertificateProof
