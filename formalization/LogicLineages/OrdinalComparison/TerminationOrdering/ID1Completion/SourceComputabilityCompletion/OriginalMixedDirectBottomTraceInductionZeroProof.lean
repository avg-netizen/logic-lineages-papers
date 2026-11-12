module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomRankedErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalMixedDirectBottomTraceInductionDefinitions OriginalMixedDirectBottomTraceInductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroAt (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hf : Nonempty (Derivation body Delta
  (fields (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) z
   s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT))) :
 Nonempty (Derivation body Delta
  (result (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) s t newParam erasedS erasedT)) := by
 let source := OriginalTransparentMixedDirectBottom.source H G M W
 let leaf := (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
 have h := andRight hf
 have hb := OriginalMixedDirectBottomTraceBaseProof.actualNilBase source leaf body alpha Delta s t cert oldParam
  (andLeft hf) (andLeft (andRight (andRight h)))
 have hc := andRight (andRight hb)
 have args := andIntro (andLeft h) (andIntro (andLeft (andRight h))
  (andIntro hc (andRight (andRight (andRight h)))))
 obtain ⟨law⟩ := OriginalMixedDirectBottomRankedErasureProof.exactRankedErasure
  H G M W oldStep body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
 obtain ⟨args⟩ := args
 exact ⟨Derivation.implicationElimination law args⟩

theorem zeroRowGeneric (source : Program 2) (leaf : Program 4)
 (hzero : ∀ (beta : Type) (Theta : List (Formula beta))
   (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm beta),
   Nonempty (Derivation body Theta (fields source leaf z s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT)) →
   Nonempty (Derivation body Theta (result source leaf s t newParam erasedS erasedT))) :
 Nonempty (Derivation body Delta
  (AtPath source
   leaf z)) := by
 apply atPathIntro
 unfold matrix
 rw [InternalTagArithmeticSyntaxProof.zRelabel]
 let A := fields source
  leaf (z : OTerm (alpha ⊕ Fin 12))
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
  (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11))
 have h : Nonempty (Derivation body (A :: Delta.map (fun q => q.relabel Sum.inl)) A) :=
  ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨out⟩ := hzero (alpha ⊕ Fin 12) _
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
  (.var (.inr 8)) (.var (.inr 9)) (.var (.inr 10)) (.var (.inr 11)) h
 exact ⟨Derivation.implicationIntroduction out⟩
theorem zeroRow (H G : Program 1) (M W : Program 2) (oldStep : Program 4) :
 Nonempty (Derivation body Delta
  (AtPath (OriginalTransparentMixedDirectBottom.source H G M W)
   (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep) z)) :=
 zeroRowGeneric (OriginalTransparentMixedDirectBottom.source H G M W)
  (OriginalTransparentMixedDirectBottom.leaf H G M W oldStep)
  (fun _ _ s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT h =>
   zeroAt H G M W oldStep s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceInductionZeroProof
