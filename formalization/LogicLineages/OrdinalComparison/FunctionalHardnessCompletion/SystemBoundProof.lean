module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemProof
open OriginalDomain FunctionalDetector SourceCollisionCompletion SourceClasses SourceTypeSupport

private theorem subtype_level (τ σ : Ty) (h : σ ∈ τ.subtypes) : σ.level ≤ τ.level := by
  induction τ with
  | ground =>
      have hs : σ = Ty.ground := by simpa [Ty.subtypes] using h
      subst σ
      exact le_rfl
  | arrow a b iha ihb =>
      simp only [Ty.subtypes,List.mem_cons,List.mem_append] at h
      rcases h with rfl | h | h
      · exact le_rfl
      · exact (iha h).trans ((Nat.le_succ _).trans (Nat.le_max_left _ _))
      · exact (ihb h).trans (Nat.le_max_right _ _)

private theorem bound_leaf {Γ τ} (t : OriginalTerm Γ τ)
    (ht : typeSupport t = τ.subtypes.toFinset) (hτ : τ.level ≤ 2) : InternalLevelBound 2 t := by
  intro σ hσ
  rw [ht] at hσ
  exact (subtype_level τ σ (List.mem_toFinset.mp hσ)).trans hτ

private theorem bound_app {Γ σ τ} (f : OriginalTerm Γ (.arrow σ τ)) (a : OriginalTerm Γ σ)
    (hτ : τ.level ≤ 2) (hf : InternalLevelBound 2 f) (ha : InternalLevelBound 2 a) :
    InternalLevelBound 2 (.app f a) := by
  intro υ hυ
  rcases Finset.mem_union.mp hυ with h | h
  · exact (subtype_level τ υ (List.mem_toFinset.mp h)).trans hτ
  · rcases Finset.mem_union.mp h with h | h
    · exact hf υ h
    · exact ha υ h

private theorem bound_lam {Γ σ τ} (b : OriginalTerm (σ::Γ) τ)
    (hτ : (Ty.arrow σ τ).level ≤ 2) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (.lam b) := by
  intro υ hυ
  rcases Finset.mem_union.mp hυ with h | h
  · exact (subtype_level (.arrow σ τ) υ (List.mem_toFinset.mp h)).trans hτ
  · exact hb υ h

private theorem bound_rename {Γ Δ τ} (r : Renaming Γ Δ) (a : OriginalTerm Γ τ)
    (ha : InternalLevelBound 2 a) : InternalLevelBound 2 (a.rename r) := by
  intro σ hσ
  rw [(SourceTypeSupportProof.supportDepthRenaming _ _ Γ Δ τ a r).1] at hσ
  exact ha σ hσ

private theorem zero_bound {Γ} : InternalLevelBound 2 (.zeroC : OriginalTerm Γ .ground) :=
  bound_leaf _ (by simp [typeSupport]) (by decide)

private theorem eraser_bound {Γ} (a b : OriginalTerm Γ .ground)
    (ha : InternalLevelBound 2 a) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (eraser a b) := by
  apply bound_app _ _ (by decide) _ hb
  exact bound_lam _ (by decide) (bound_rename _ a ha)

private theorem ground_detector_bound {Γ} (a b : OriginalTerm Γ .ground)
    (ha : InternalLevelBound 2 a) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (detectorLeft a b) ∧ InternalLevelBound 2 (detectorRight a b) := by
  exact ⟨eraser_bound _ _ (eraser_bound _ _ ha ha) (eraser_bound _ _ hb hb),
    eraser_bound _ _ (eraser_bound _ _ ha hb) (eraser_bound _ _ hb ha)⟩

private theorem pad_bound {Γ} (a : OriginalTerm Γ unary) (q : OriginalTerm Γ .ground)
    (ha : InternalLevelBound 2 a) (hq : InternalLevelBound 2 q) :
    InternalLevelBound 2 (pad a q) := by
  apply bound_app _ _ (by decide) _ hq
  exact bound_lam _ (by decide) (bound_rename _ a ha)

private theorem aligned_bound {Γ} (a : OriginalTerm Γ unary) (ha : InternalLevelBound 2 a) :
    InternalLevelBound 2 (alignedLeft a) ∧ InternalLevelBound 2 (alignedRight a) := by
  have har := bound_rename (shiftTwo Γ) a ha
  exact ⟨pad_bound _ _ har (bound_leaf _ (by simp [typeSupport]) (by decide)),
    pad_bound _ _ har (bound_leaf _ (by simp [typeSupport]) (by decide))⟩

private theorem payload_bound {Γ} (a b : OriginalTerm Γ unary)
    (ha : InternalLevelBound 2 a) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (payload a b) := by
  apply bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ hb ha)
  apply bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ ha hb)
  apply bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ hb hb)
  exact bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ ha ha) zero_bound

private theorem functional_detector_bound {Γ} (a b : OriginalTerm Γ unary)
    (ha : InternalLevelBound 2 a) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (left a b) ∧ InternalLevelBound 2 (right a b) := by
  have hq := payload_bound a b ha hb
  exact ⟨eraser_bound _ _
    (bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ ha ha) hq)
    (bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ hb hb) hq),
    eraser_bound _ _
    (bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ ha hb) hq)
    (bound_app _ _ (by decide) (SignedPair.Proof.combine_bound _ _ hb ha) hq)⟩

private theorem aggregate_bound {Γ} (ps : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground))
    (hp : ∀ p ∈ ps, InternalLevelBound 2 p.1 ∧ InternalLevelBound 2 p.2) :
    InternalLevelBound 2 (SourceAggregateCompletion.aggregate ps).1 ∧
    InternalLevelBound 2 (SourceAggregateCompletion.aggregate ps).2 := by
  induction ps with
  | nil => exact ⟨zero_bound,zero_bound⟩
  | cons p ps ih =>
      have hpair := hp p (List.mem_cons_self)
      have ht := ih (fun q hq => hp q (List.mem_cons_of_mem _ hq))
      have hd := ground_detector_bound p.1 p.2 hpair.1 hpair.2
      exact ⟨eraser_bound _ _ hd.1 ht.1, eraser_bound _ _ hd.2 ht.2⟩

theorem compiled_detectors_bound {n : Nat} (s : System n) :
    ∀ p ∈ (compileSystem s).detectors, InternalLevelBound 2 p.1 ∧ InternalLevelBound 2 p.2 := by
  induction s with
  | nil =>
      intro p hp
      exact False.elim (List.not_mem_nil hp)
  | cons d ds ih =>
      intro p hp
      have hc := SignedPair.Proof.compiler_bound d
      have ha := bound_rename (compileSystem ds).original _ hc.1
      have hb := bound_rename (compileSystem ds).original _ hc.2
      simp only [compileSystem] at hp
      rcases List.mem_cons.mp hp with hp | hp
      · subst p
        exact functional_detector_bound _ _ (aligned_bound _ ha).1 (aligned_bound _ hb).2
      · obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hp
        have hq' := ih q hq
        exact ⟨bound_rename _ _ hq'.1, bound_rename _ _ hq'.2⟩

theorem compiled_context_bound {n : Nat} (s : System n) :
    ∀ τ ∈ (compileSystem s).context, τ.level ≤ 1 := by
  induction s with
  | nil =>
      intro τ hτ
      simp only [compileSystem, SignedPair.Context, List.mem_replicate] at hτ
      rcases hτ with ⟨_,rfl⟩
      decide
  | cons d ds ih =>
      intro τ hτ
      simp only [compileSystem, List.mem_cons] at hτ
      rcases hτ with rfl | rfl | hτ
      · decide
      · decide
      · exact ih τ hτ

theorem levelTwoBounds : SystemSourceTargets.LevelTwoBounds := by
  intro n s
  have hs := aggregate_bound (compileSystem s).detectors (compiled_detectors_bound s)
  have hi : InternalLevelBound 2 (@GroundEquivalence.identity (compileSystem s).context) :=
    SignedPair.Proof.identity_bound
  have hc : InternalLevelBound 2 (@GroundEquivalence.constant (compileSystem s).context) :=
    bound_lam _ (by decide) zero_bound
  exact ⟨compiled_context_bound s, hs.1, hs.2,
    bound_app _ _ (by decide) hc hs.2, bound_app _ _ (by decide) hi hs.1⟩

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SystemProof
