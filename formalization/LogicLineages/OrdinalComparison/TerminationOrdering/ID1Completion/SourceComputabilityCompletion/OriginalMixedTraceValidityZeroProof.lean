module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalBottomSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomEndpointProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalBooleanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedTraceValidityDefinitions OriginalMixedTraceValidityBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroAt (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t cert oldParam : OTerm alpha)
 (hf : Nonempty (Derivation body Delta
  (fields (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) z s t cert oldParam))) :
 Nonempty (Derivation body Delta
  (result (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) t oldParam)) := by
 have hb := OriginalMixedDirectBottomTraceBaseProof.actualNilBase
  (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) body alpha Delta s t cert oldParam
  (andLeft hf) (andRight (andRight hf))
 apply InternalAcceptanceSupportProof.programCases InternalUnpair.left ![s] _
 intro beta j Theta typ incl ht
 rw [OriginalMixedTraceValiditySyntaxProof.resultRename]
 have hb' := InternalGraphCompositionFunctionalityProof.renameInto hb j Theta incl
 have hs' := InternalGraphCompositionFunctionalityProof.renameInto (andLeft (andRight hf)) j Theta incl
 simp only [InternalApplicationCertificateConstructorsSyntaxProof.graph2Rename,
  InternalApplicationCertificateConstructorsSyntaxProof.graph4Rename,
  InternalApplicationCertificateConstructorsSyntaxProof.graph1Rename,
  OriginalUniverseDecoderInternalBooleanProof.andRename,
  OriginalRawSyntaxTransportInternalParserSyntaxProof.numeralRename] at hb' hs'
 have hbottom := OriginalMixedDirectBottomEndpointProof.endpoint H G M W oldStep
  (s.relabel j) (t.relabel j) (cert.relabel j) (oldParam.relabel j) typ
  (andRight (andRight hb')) ht (andLeft (andRight hb'))
 exact OriginalInternalBottomSourceProof.bottomSource H G M W body beta Theta
  (s.relabel j) (t.relabel j) (oldParam.relabel j) typ hs' ht hbottom

theorem zeroRowGeneric (source : Program 2) (leaf : Program 4)
 (hzero : ∀ (beta : Type) (Theta : List (Formula beta))
   (s t cert oldParam  : OTerm beta),
   Nonempty (Derivation body Theta (fields source leaf z s t cert oldParam)) →
   Nonempty (Derivation body Theta (result source leaf t oldParam))) :
 Nonempty (Derivation body Delta
  (AtPath source
   leaf z)) := by
 apply atPathIntro
 unfold matrix
 rw [InternalTagArithmeticSyntaxProof.zRelabel]
 let A := fields source
  leaf (z : OTerm (alpha ⊕ Fin 4))
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
 have h : Nonempty (Derivation body (A :: Delta.map (fun q => q.relabel Sum.inl)) A) :=
  ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨out⟩ := hzero (alpha ⊕ Fin 4) _
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) h
 exact ⟨Derivation.implicationIntroduction out⟩
theorem zeroRow (H G : Program 1) (M W : Program 2) (oldStep : Program 4) :
 Nonempty (Derivation body Delta
  (AtPath (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) z)) :=
 zeroRowGeneric (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  (fun _ _ s t cert oldParam h =>
   zeroAt H G M W oldStep s t cert oldParam h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedTraceValidityZeroProof
