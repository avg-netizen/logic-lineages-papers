module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathCoordinateProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepInternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof InternalApplicationStepPeelSupportProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTransparentMixedPathInternalDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

def queries : Fin 5 → Program 12 := ![
 leftOf (.projection 6),rightOf (.projection 6),
 consOf (two 12) (leftOf (.projection 6)),
 .composition OriginalHereditaryLambda.live ![.projection 0,.projection 1,.projection 2,.projection 3],
 .composition OriginalHereditaryLambda.live ![.projection 4,.projection 5,.projection 6,.projection 3] ]

theorem atWitnesses (source : Program 2) (oldStep : Program 4)
 (s t cert parameter childS childT childCert arg d e arrow out tail payload code state next : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow)))
 (hl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail childCert)))
 (hr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right payload childCert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code (suc (suc z)) tail)))
 (hs : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
 (hn : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live next childS childT childCert parameter))) :
 Nonempty (Derivation body Delta ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
  (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert parameter))) := by
 have hprefix := andRight (andRight (andRight (andRight (andRight (andRight (andRight hh))))))
 have hcons := binaryValue InternalListCodec.consCode (two 1) InternalUnpair.left code (suc (suc z)) tail ![childCert]
  hc (twoValue ![childCert]) hl
 have hp := binaryRecover InternalPairing.pairing prefixedPath InternalUnpair.right cert code payload ![childCert] hprefix hcons hr
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 let ys : Fin 4 → OTerm alpha := ![childS,childT,childCert,parameter]
 have hpath := unaryValue InternalUnpair.left (.projection 2) code cert xs
  (pairLeft cert code payload hp) (projectionValue 2 xs)
 have hchildpath := unaryValue InternalUnpair.left (.projection 2) tail childCert ys hl (projectionValue 2 ys)
 exact OriginalTransparentMixedPathCoordinateProof.actualApplicationEquivalence source oldStep body alpha Delta
  s t cert parameter childS childT childCert arg d e arrow code (suc (suc z)) tail state next out hh hpath hchildpath hs hn hc

theorem hop (source : Program 2) (oldStep : Program 4)
 (s t cert parameter childS childT childCert arg d e arrow out : OTerm alpha)
 (h : Nonempty (Derivation body Delta (ApplicationHop source s t cert parameter childS childT childCert arg d e arrow))) :
 Nonempty (Derivation body Delta ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
  (graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out childS childT childCert parameter))) := by
 let xs : Fin 12 → OTerm alpha := ![s,t,cert,parameter,childS,childT,childCert,arg,d,e,arrow,out]
 apply queryCases queries xs _
 intro beta j ys Gamma hj hq
 have h' := renameInto h j Gamma hj
 simp only [ApplicationHop,conjunctionRename,graph1Rename,graph2Rename,graph4Rename,
  SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel] at h'
 let xx : Fin 12 → OTerm beta := fun i => (xs i).relabel j
 have hleft := unaryRecover InternalUnpair.left (.projection (6 : Fin 12)) (ys 0) (childCert.relabel j) xx (hq 0) (projectionValue 6 xx)
 have hright := unaryRecover InternalUnpair.right (.projection (6 : Fin 12)) (ys 1) (childCert.relabel j) xx (hq 1) (projectionValue 6 xx)
 have hcons := binaryRecover InternalListCodec.consCode (two 12) (leftOf (.projection 6))
  (ys 2) (suc (suc z)) (ys 0) xx (hq 2) (twoValue xx) (hq 0)
 have hstate := OriginalTransparentLambdaStepInternalProof.wireRecover OriginalHereditaryLambda.live
  (![0,1,2,3] : Fin 4 → Fin 12) (ys 3) xx (hq 3)
 have hnext := OriginalTransparentLambdaStepInternalProof.wireRecover OriginalHereditaryLambda.live
  (![4,5,6,3] : Fin 4 → Fin 12) (ys 4) xx (hq 4)
 have he1 : (fun i => xx ((![0,1,2,3] : Fin 4 → Fin 12) i)) =
  ![s.relabel j,t.relabel j,cert.relabel j,parameter.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
 have he2 : (fun i => xx ((![4,5,6,3] : Fin 4 → Fin 12) i)) =
  ![childS.relabel j,childT.relabel j,childCert.relabel j,parameter.relabel j] := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun i => Fin.elim0 i)))) i
 rw [he1] at hstate
 rw [he2] at hnext
 have hout := atWitnesses source oldStep (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
  (childS.relabel j) (childT.relabel j) (childCert.relabel j) (arg.relabel j) (d.relabel j) (e.relabel j) (arrow.relabel j)
  (out.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) h' hleft hright hcons hstate hnext
 simpa only [OriginalTransparentLambdaStepInternalProof.iffRename,graph4Rename] using hout

theorem actualApplicationPrefix : OriginalTransparentMixedPathApplicationPrefixTargets.ActualApplicationPrefix := by
 intro source oldStep body alpha Delta s t cert parameter childS childT childCert arg d e arrow out
 let A := ApplicationHop source s t cert parameter childS childT childCert arg d e arrow
 obtain ⟨hout⟩ := hop source oldStep s t cert parameter childS childT childCert arg d e arrow out
  (show Nonempty (Derivation body (A :: Delta) A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 exact ⟨Derivation.implicationIntroduction hout⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathApplicationPrefixProof
