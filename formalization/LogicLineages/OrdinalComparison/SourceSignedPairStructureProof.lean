module
public import LogicLineages.OrdinalComparison.SourceSignedPairTargets
public import LogicLineages.OrdinalComparison.SourceTypeSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair.Proof
open SourceClasses SourceTypeSupport FunctionalDetector

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
    (ht : typeSupport t = τ.subtypes.toFinset) (hτ : τ.level≤2) : InternalLevelBound 2 t := by
  intro σ hσ
  rw [ht] at hσ
  exact (subtype_level τ σ (List.mem_toFinset.mp hσ)).trans hτ

private theorem bound_app {Γ σ τ} (f : OriginalTerm Γ (.arrow σ τ)) (a : OriginalTerm Γ σ)
    (hτ : τ.level≤2) (hf : InternalLevelBound 2 f) (ha : InternalLevelBound 2 a) :
    InternalLevelBound 2 (.app f a) := by
  intro υ hυ
  rcases Finset.mem_union.mp hυ with h | h
  · exact (subtype_level τ υ (List.mem_toFinset.mp h)).trans hτ
  · rcases Finset.mem_union.mp h with h | h
    · exact hf υ h
    · exact ha υ h

private theorem bound_lam {Γ σ τ} (b : OriginalTerm (σ::Γ) τ)
    (hτ : (Ty.arrow σ τ).level≤2) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (.lam b) := by
  intro υ hυ
  rcases Finset.mem_union.mp hυ with h | h
  · exact (subtype_level (.arrow σ τ) υ (List.mem_toFinset.mp h)).trans hτ
  · exact hb υ h

private theorem bound_rename {Γ Δ τ} (a : OriginalTerm Γ τ) (r : Renaming Γ Δ)
    (ha : InternalLevelBound 2 a) : InternalLevelBound 2 (a.rename r) := by
  intro σ hσ
  rw [(SourceTypeSupportProof.supportDepthRenaming _ _ Γ Δ τ a r).1] at hσ
  exact ha σ hσ

theorem identity_bound {Γ} : InternalLevelBound 2 (@identity Γ) := by
  apply bound_lam _ (by decide)
  apply bound_leaf _ (by simp [typeSupport]) (by decide)

theorem project_bound {Γ} (a b : OriginalTerm Γ unary)
    (ha : InternalLevelBound 2 a) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (project a b) := by
  apply bound_app _ _ (by decide) _ hb
  exact bound_lam _ (by decide) (bound_rename a _ ha)

theorem combine_bound {Γ} (a b : OriginalTerm Γ unary)
    (ha : InternalLevelBound 2 a) (hb : InternalLevelBound 2 b) :
    InternalLevelBound 2 (combine a b) := by
  apply bound_app _ _ (by decide)
  · exact bound_lam _ (by decide) (bound_rename a _ ha)
  · exact bound_lam _ (by decide) (bound_rename b _ hb)

theorem omega_bound {Γ} (a : OriginalTerm Γ unary) (ha : InternalLevelBound 2 a) :
    InternalLevelBound 2 (liftOmega a) := by
  apply bound_app _ _ (by decide)
  · apply bound_app _ _ (by decide)
    · exact bound_leaf _ (by simp [typeSupport]) (by decide)
    · exact bound_leaf _ (by simp [typeSupport]) (by decide)
  · exact bound_lam _ (by decide) (bound_rename a _ ha)

def PairBound {Γ} (p : Pair Γ) : Prop := InternalLevelBound 2 p.1 ∧ InternalLevelBound 2 p.2

theorem join_bound {Γ} (p q : Pair Γ) (hp : PairBound p) (hq : PairBound q) : PairBound (join p q) :=
  ⟨combine_bound _ _ hp.1 hq.1,combine_bound _ _ hp.2 hq.2⟩
theorem eight_bound {Γ} (p : Pair Γ) (hp : PairBound p) : PairBound (timesEight p) :=
  ⟨combine_bound _ _ hp.1 identity_bound,combine_bound _ _ hp.2 identity_bound⟩
theorem sixteen_bound {Γ} (p : Pair Γ) (hp : PairBound p) : PairBound (timesSixteen p) :=
  join_bound p p hp hp

private theorem iterate_bound {Γ} (f : Pair Γ → Pair Γ)
    (hf : ∀p, PairBound p → PairBound (f p)) (k : Nat) (p : Pair Γ) (hp : PairBound p) :
    PairBound ((f^[k]) p) := by
  induction k with
  | zero => exact hp
  | succ k ih => rw [Function.iterate_succ_apply']; exact hf _ ih

private theorem balanced_bound {Γ} (d : Nat) (f : Nat → Pair Γ)
    (hf : ∀i, PairBound (f i)) (o : Nat) : PairBound (balanced d f o) := by
  induction d generalizing o with
  | zero => exact hf o
  | succ d ih => exact join_bound _ _ (ih o) (ih (o+2^d))

theorem unit_bound {Γ} : PairBound (@unitPair Γ) := by
  apply balanced_bound
  intro i
  unfold constantLeaf
  split
  · exact ⟨combine_bound _ _ identity_bound identity_bound,project_bound _ _ identity_bound identity_bound⟩
  · split
    · exact ⟨identity_bound,project_bound _ _ identity_bound identity_bound⟩
    · exact ⟨identity_bound,identity_bound⟩

theorem variable_bound {n} (i : Fin n) : PairBound (variablePair i) := by
  apply join_bound _ _ _ unit_bound
  apply iterate_bound _ eight_bound
  exact ⟨project_bound _ _ (bound_leaf _ (by simp [typeSupport]) (by decide)) identity_bound,
    project_bound _ _ identity_bound identity_bound⟩

theorem pad_bound {Γ} (d : Nat) (p : Pair Γ) (hp : PairBound p) : PairBound (pad d p) :=
  iterate_bound _ sixteen_bound _ _ (iterate_bound _ eight_bound _ _ hp)

theorem compiler_bound {n} (d : Expression n) : PairBound (compile d).pair := by
  induction d with
  | unit => exact unit_bound
  | var i => exact variable_bound i
  | add a b iha ihb => exact join_bound _ _ (pad_bound _ _ iha) (pad_bound _ _ ihb)
  | neg a ih => exact ⟨ih.2,ih.1⟩
  | shift a ih => exact ⟨omega_bound _ ih.1,omega_bound _ ih.2⟩
end LogicLineages.OrdinalComparison.Source.SignedPair.Proof
