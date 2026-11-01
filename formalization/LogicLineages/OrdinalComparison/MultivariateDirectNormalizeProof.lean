module
public import LogicLineages.OrdinalComparison.MultivariateDirectNormalizeTargets
public import LogicLineages.OrdinalComparison.MultivariateClosedFoldProof
public import LogicLineages.OrdinalComparison.MultivariateDecodeAddProof
public import LogicLineages.OrdinalComparison.MultivariateCollectedIdentityProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateDirectNormalize

attribute [local irreducible] Phi actualCollapse encodedPositiveFoldValue encodedMultivariateClosedValue

private theorem decode_constant (cap c : Nat) :
    decodeMultivariateCollected cap (.mk c 0 .nil)=.mk c [] .nil := by
  simp [decodeMultivariateCollected,decodeMultivariateCollectedTags,multivariateCollectedAdd,
    multivariateCoefficientAdd,multivariateCollectedTagsMerge]

private theorem decode_original_head (cap : Nat) (rho : NONote) (A : CollectedPositiveNF)
    (hi : positiveVariableHeadIndex cap rho=none) :
    decodeMultivariateCollected cap (.mk 0 0 (.cons rho A 1 .nil))=
      .mk 0 [] (.cons rho (decodeMultivariateCollected cap A) 1 .nil) := by
  simp [decodeMultivariateCollected,decodeMultivariateCollectedTags,hi,multivariateCollectedAdd,
    multivariateCoefficientAdd,multivariateCollectedTagsMerge,multivariateCollectedTagInsert]

private theorem normalization_correspondence (d cap : Nat) (E : MultivariatePositiveExpr) :
    multivariatePositiveValid d E → multivariatePositiveEncode E≤cap →
      multivariateCollectedNormalizeAt cap E=multivariateCollectedNormalize E := by
  induction E with
  | constant c =>
    intro _ _
    exact decode_constant cap c
  | input i =>
    intro _ _
    have hi := (MultivariateFreshProbe.head_source.1 cap i).2.2.2
    have hz : multivariateCoefficientAdd (multivariateVariableCoefficients i 1) []=
        multivariateVariableCoefficients i 1 := by
      cases multivariateVariableCoefficients i 1 <;> rfl
    simp [multivariateCollectedNormalizeAt,multivariatePositiveProbe,collectedPositiveNormalize,
      collectedPositiveSupport,collectedTagsSupport,decodeMultivariateCollected,
      decodeMultivariateCollectedTags,hi,multivariateCollectedNormalize,multivariateCollectedAdd,
      multivariateCoefficientAdd,multivariateCollectedTagsMerge,hz]
  | add E F ihE ihF =>
    intro hv hc
    have hl := Nat.left_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
    have hr := Nat.right_le_pair (multivariatePositiveEncode E) (multivariatePositiveEncode F)
    have he : multivariatePositiveEncode E≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    have hf : multivariatePositiveEncode F≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    change decodeMultivariateCollected cap (collectedPositiveAdd
      (collectedPositiveNormalize (multivariatePositiveProbe cap E))
      (collectedPositiveNormalize (multivariatePositiveProbe cap F)))=_
    rw [decode_add]
    change multivariateCollectedAdd (multivariateCollectedNormalizeAt cap E)
      (multivariateCollectedNormalizeAt cap F)=_
    rw [ihE hv.1 he,ihF hv.2 hf]
    rfl
  | head rho E ih =>
    intro hv hc
    have hl := Nat.left_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)
    have hr := Nat.right_le_pair (rawNoteEncode rho.1) (multivariatePositiveEncode E)
    have hh : rawNoteEncode rho.1≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    have he : multivariatePositiveEncode E≤cap := by
      simp only [multivariatePositiveEncode] at hc; omega
    have hp := MultivariateFreshProbe.source.1 d cap E hv.2.2
    have hs := (collectedPositiveNormalizeSupport (multivariatePositiveProbe cap E) hp).trans
      (probe_support cap E)
    change decodeMultivariateCollected cap (collectedPositiveNormalize (.head rho
      (multivariatePositiveProbe cap E)))=multivariateCollectedNormalize (.head rho E)
    by_cases hz : multivariatePositiveHasInput E=false
    · rw [collectedPositiveNormalize,if_pos (hs.trans hz),decode_constant,
        multivariateCollectedNormalize,if_pos hz]
      exact congrArg (fun n => MultivariateCollectedNF.mk n [] .nil)
        (closed_probe_fold cap (.head rho E) hz)
    · have hn : collectedPositiveSupport
          (collectedPositiveNormalize (multivariatePositiveProbe cap E))≠false := by rwa [hs]
      rw [collectedPositiveNormalize,if_neg hn,decode_original_head cap rho _
        (MultivariateFreshProbe.head_source.2.1 cap rho hh),multivariateCollectedNormalize,if_neg hz]
      exact congrArg (fun A => MultivariateCollectedNF.mk 0 [] (.cons rho A 1 .nil))
        (ih hv.2.2 he)

theorem correspondence : Targets.MultivariateDirectNormalizeCorrespondence := normalization_correspondence

theorem source : Targets.MultivariateDirectNormalizeSource := by
  intro d E hv rho
  have h := MultivariateCollected.source_semantics d (multivariatePositiveEncode E) E hv (Nat.le_refl _) rho
  rwa [correspondence d (multivariatePositiveEncode E) E hv (Nat.le_refl _)] at h

theorem complete : Targets.MultivariateDirectNormalizeComplete := by
  intro d E F hE hF
  let cap := max (multivariatePositiveEncode E) (multivariatePositiveEncode F)
  have hcE : multivariatePositiveEncode E≤cap := Nat.le_max_left _ _
  have hcF : multivariatePositiveEncode F≤cap := Nat.le_max_right _ _
  have h := MultivariateCollected.common_signature_identity d cap E F hE hF hcE hcF
  rwa [correspondence d cap E hE hcE,correspondence d cap F hF hcF] at h

theorem cap_independent : Targets.MultivariateCollectedCapIndependent := by
  intro d cap cap' E hv hc hc'
  exact (correspondence d cap E hv hc).trans (correspondence d cap' E hv hc').symm

end LogicLineages.OrdinalComparison.MultivariateDirectNormalize
