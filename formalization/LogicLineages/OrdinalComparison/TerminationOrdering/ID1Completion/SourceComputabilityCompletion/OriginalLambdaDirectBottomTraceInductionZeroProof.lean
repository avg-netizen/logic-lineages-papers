module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomRankedErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionZeroProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (z)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTraceInductionDefinitions OriginalLambdaDirectBottomTraceInductionBindingProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroAt (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT : OTerm alpha)
 (hf : Nonempty (Derivation body Delta
  (fields (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep z
   s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT))) :
 Nonempty (Derivation body Delta
  (result (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep s t newParam erasedS erasedT)) := by
 let source := OriginalTransparentDirectBottomGlobal.source p H G W
 let leaf := (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep
 have h := andRight hf
 have hb := OriginalLambdaDirectBottomTraceBaseProof.actualNilBase source leaf body alpha Delta s t cert oldParam
  (andLeft hf) (andLeft (andRight (andRight h)))
 have hc := andRight (andRight hb)
 have args := andIntro (andLeft h) (andIntro (andLeft (andRight h))
  (andIntro hc (andRight (andRight (andRight h)))))
 obtain ⟨law⟩ := OriginalTransparentDirectBottomRankedErasureProof.exactRankedErasure
  p H G W P body alpha Delta s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT
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
theorem zeroRow (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3) :
 Nonempty (Derivation body Delta
  (AtPath (OriginalTransparentDirectBottomGlobal.source p H G W)
   (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep z)) :=
 zeroRowGeneric (OriginalTransparentDirectBottomGlobal.source p H G W)
  (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep
  (fun _ _ s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT h =>
   zeroAt p H G W P s t cert oldParam newParam gamma extended d cutoff c erasedS erasedT h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionZeroProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceInductionZeroProof
