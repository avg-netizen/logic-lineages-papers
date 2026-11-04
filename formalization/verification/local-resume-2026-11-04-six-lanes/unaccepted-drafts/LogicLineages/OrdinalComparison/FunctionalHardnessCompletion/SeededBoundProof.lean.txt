module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededCompilerTargets
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaPairProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Proof
open OriginalDomain FunctionalDetector SignedPair SourceClasses SourceTypeSupport

private theorem subtype_level (τ σ : Ty) (h : σ∈τ.subtypes) : σ.level≤τ.level := by
  induction τ with
  | ground =>
      have he : σ=.ground := by simpa [Ty.subtypes] using h
      subst σ
      exact le_rfl
  | arrow a b ha hb =>
      simp only [Ty.subtypes,List.mem_cons,List.mem_append] at h
      rcases h with rfl | h | h
      · exact le_rfl
      · exact (ha h).trans ((Nat.le_succ _).trans (Nat.le_max_left _ _))
      · exact (hb h).trans (Nat.le_max_right _ _)

theorem leaf_bound {Γ τ} (a : OriginalTerm Γ τ)
    (ha : typeSupport a=τ.subtypes.toFinset) (hτ : τ.level≤3) : InternalLevelBound 3 a := by
  intro σ hσ
  rw [ha] at hσ
  exact (subtype_level τ σ (List.mem_toFinset.mp hσ)).trans hτ

theorem app_bound {Γ σ τ} (f : OriginalTerm Γ (.arrow σ τ)) (a : OriginalTerm Γ σ)
    (hτ : τ.level≤3) (hf : InternalLevelBound 3 f) (ha : InternalLevelBound 3 a) :
    InternalLevelBound 3 (.app f a) := by
  intro υ hυ
  rcases Finset.mem_union.mp hυ with h | h
  · exact (subtype_level τ υ (List.mem_toFinset.mp h)).trans hτ
  · rcases Finset.mem_union.mp h with h | h
    · exact hf υ h
    · exact ha υ h

theorem lam_bound {Γ σ τ} (b : OriginalTerm (σ::Γ) τ)
    (hτ : (Ty.arrow σ τ).level≤3) (hb : InternalLevelBound 3 b) :
    InternalLevelBound 3 (.lam b) := by
  intro υ hυ
  rcases Finset.mem_union.mp hυ with h | h
  · exact (subtype_level (.arrow σ τ) υ (List.mem_toFinset.mp h)).trans hτ
  · exact hb υ h

theorem rename_bound {Γ Δ τ} (a : OriginalTerm Γ τ) (r : Renaming Γ Δ)
    (ha : InternalLevelBound 3 a) : InternalLevelBound 3 (a.rename r) := by
  intro σ hσ
  rw [(SourceTypeSupportProof.supportDepthRenaming _ _ Γ Δ τ a r).1] at hσ
  exact ha σ hσ

theorem monotone_bound {Γ τ} (a : OriginalTerm Γ τ)
    (ha : InternalLevelBound 2 a) : InternalLevelBound 3 a :=
  fun σ hσ => (ha σ hσ).trans (by decide)

theorem combine_bound {Γ} (a b : OriginalTerm Γ unary)
    (ha : InternalLevelBound 3 a) (hb : InternalLevelBound 3 b) :
    InternalLevelBound 3 (combine a b) := by
  apply app_bound _ _ (by decide)
  · exact lam_bound _ (by decide) (rename_bound a _ ha)
  · exact lam_bound _ (by decide) (rename_bound b _ hb)

private theorem omega_bound {Γ} (a : OriginalTerm Γ unary)
    (ha : InternalLevelBound 3 a) : InternalLevelBound 3 (liftOmega a) := by
  apply app_bound _ _ (by decide)
  · apply app_bound _ _ (by decide)
    · exact leaf_bound _ (by simp [typeSupport]) (by decide)
    · exact leaf_bound _ (by simp [typeSupport]) (by decide)
  · exact lam_bound _ (by decide) (rename_bound a _ ha)

def PairBound {Γ} (p : Pair Γ) : Prop :=
  InternalLevelBound 3 p.1 ∧ InternalLevelBound 3 p.2

private theorem join_bound {Γ} (p q : Pair Γ) (hp : PairBound p) (hq : PairBound q) :
    PairBound (join p q) :=
  ⟨combine_bound _ _ hp.1 hq.1,combine_bound _ _ hp.2 hq.2⟩

private theorem eight_bound {Γ} (p : Pair Γ) (hp : PairBound p) : PairBound (timesEight p) :=
  ⟨combine_bound _ _ hp.1 (monotone_bound _ SignedPair.Proof.identity_bound),
   combine_bound _ _ hp.2 (monotone_bound _ SignedPair.Proof.identity_bound)⟩

private theorem sixteen_bound {Γ} (p : Pair Γ) (hp : PairBound p) : PairBound (timesSixteen p) :=
  join_bound p p hp hp

private theorem iterate_bound {Γ} (f : Pair Γ→Pair Γ)
    (hf : ∀p,PairBound p→PairBound (f p)) (k : Nat) (p : Pair Γ) (hp : PairBound p) :
    PairBound ((f^[k]) p) := by
  induction k with
  | zero => exact hp
  | succ k ih => rw [Function.iterate_succ_apply']; exact hf _ ih

private theorem pad_bound {Γ} (d : Nat) (p : Pair Γ) (hp : PairBound p) : PairBound (pad d p) :=
  iterate_bound _ sixteen_bound _ _ (iterate_bound _ eight_bound _ _ hp)

private theorem seed_bound {Γ} : PairBound (@OmegaSeed.pair Γ) := by
  constructor
  · exact app_bound _ _ (by decide) (OmegaSeed.Proof.source_bound Γ)
      (monotone_bound _ SignedPair.Proof.unit_bound.1)
  · exact app_bound _ _ (by decide) (OmegaSeed.Proof.source_bound Γ)
      (monotone_bound _ SignedPair.Proof.unit_bound.2)

theorem compiler_bound {n : Nat} (d : Expression (n+1)) : PairBound (compile d).pair := by
  induction d with
  | unit => exact ⟨monotone_bound _ SignedPair.Proof.unit_bound.1,
      monotone_bound _ SignedPair.Proof.unit_bound.2⟩
  | var i =>
      unfold compile
      split
      · exact ⟨monotone_bound _ (SignedPair.Proof.variable_bound _).1,
          monotone_bound _ (SignedPair.Proof.variable_bound _).2⟩
      · exact seed_bound
  | neg a ha => exact ⟨ha.2,ha.1⟩
  | shift a ha => exact ⟨omega_bound _ ha.1,omega_bound _ ha.2⟩
  | add a b ha hb => exact join_bound _ _ (pad_bound _ _ ha) (pad_bound _ _ hb)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler.Proof
