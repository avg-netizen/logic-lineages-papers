module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointValidityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityApplicationSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedImplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedStructuralEndpointGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableCanonicalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointValidityProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTransparentDecoderValidatorCollapsePackedProof
open OriginalRawSyntaxTransportInternalParserSyntaxProof (numeralRename)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedLiteralEndpointDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem atParameter (H G : Program 1) (M W : Program 2)
 (s t cert parameter fn targetFn childCert arg d e arrow fp ap c gamma : OTerm alpha)
 (hcs : Nonempty (Derivation body Delta (InternalApplicationValidityClosure.applicationConstructors arrow d e fp ap fn arg s)))
 (hh : Nonempty (Derivation body Delta (OriginalTransparentMixedPathInternalDefinitions.ApplicationHop
  (OriginalUniverseDecoder.source H G M W) s t cert parameter fn targetFn childCert arg d e arrow)))
 (hr : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) targetFn parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma))) :
 Nonempty (Derivation body Delta (InternalParameterizedApplicationStepChecker.endpointGraph
  (endpoint H G M W) (numeral 1) d e fn targetFn arg parameter)) := by
 have hfields := OriginalMixedTraceValidityApplicationSourceProof.fieldsIff H G M W
  arrow d e fp ap fn arg s parameter c gamma hcs hp
 have hv := OriginalFinalVariableCanonicalSupportProof.iffForward hfields (andLeft hh)
 have hfn := andLeft (andRight hv)
 have harg := andRight (andRight hv)
 have ht := OriginalTransparentDecoderValidatorCollapsePackedImplicationProof.sourceToTarget H G M W targetFn parameter hr
 let xs : Fin 2 → OTerm alpha := ![e,parameter]
 have hc := unaryValue InternalUnpair.left (.projection 1) c parameter xs (pairLeft parameter c gamma hp)
  (projectionValue 1 xs)
 have hm := binaryValue M (.projection 0) (leftOf (.projection 1)) (numeral 1) e c xs
  (andLeft hv) (projectionValue 0 xs) hc
 have htags := andIntro (andLeft (andRight (andRight (andRight (andRight hh)))))
  (andIntro (andLeft (andRight (andRight (andRight (andRight (andRight hh))))))
   (andLeft (andRight (andRight (andRight (andRight (andRight (andRight hh))))))))
 exact InternalParameterizedStructuralEndpointGuardSupportProof.endpointAccept
  (OriginalUniverseDecoder.source H G M W) (OriginalTypedDecoder.target H G) (memberAt M)
  arrow d e fn targetFn arg parameter (andLeft hcs)
  (andIntro hfn (andIntro ht (andIntro harg (andIntro htags hm))))

theorem actualEndpointFromTargetSource : OriginalMixedLiteralEndpointValidityTargets.ActualEndpointFromTargetSource := by
 intro H G M W body alpha Delta s t cert parameter fn targetFn childCert arg d e arrow fp ap hcs hh hr
 apply packedCases s parameter _
 intro beta j Theta typ raw c gamma incl _ hp
 simp only [InternalParameterizedApplicationStepCheckerSyntaxProof.endpointGraphRename,numeralRename]
 have hcs' := renameInto hcs j Theta incl
 have hh' := renameInto hh j Theta incl
 have hr' := renameInto hr j Theta incl
 simp only [InternalApplicationValidityClosure.applicationConstructors,
  OriginalUniverseDecoderInternalBooleanProof.andRename,graph2Rename,graph4Rename] at hcs'
 simp only [OriginalTransparentMixedPathInternalDefinitions.ApplicationHop,
  OriginalUniverseDecoderInternalBooleanProof.andRename,graph1Rename,graph2Rename,graph4Rename,numeralRename] at hh'
 simp only [graph2Rename,numeralRename] at hr'
 exact atParameter H G M W (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j)
  (fn.relabel j) (targetFn.relabel j) (childCert.relabel j) (arg.relabel j)
  (d.relabel j) (e.relabel j) (arrow.relabel j) (fp.relabel j) (ap.relabel j) c gamma hcs' hh' hr' hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointValidityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedLiteralEndpointValidityProof
