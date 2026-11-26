module
public import LogicLineages.PermittedControl.SelectedDescentNormProof
public import LogicLineages.PermittedControl.SelectedSourceDomainProof
public import LogicLineages.PermittedControl.SelectedHeadClosureProof
public import LogicLineages.PermittedControl.SelectedSupportProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedFirstFreeProof
open OrdinalComparison Source SelectedSourceDomain SelectedFirstFree

private theorem scalar_value_norm (ctrl : Nat → Nat) (Γ : List Ty)
    (ρ : AdmissibleSubstitution ctrl Γ) (t : OrdinalExpression Γ) (ht : AmbientGrade ctrl Γ 0 t) :
    actualOrdinalNorm (expressionValue ctrl ρ t) = finiteValue (expressionValue ctrl ρ t) := by
  obtain ⟨n,hn,hc,hN⟩ := SourceScalarCalibrationProof.scalarCalibration.2.2 ctrl Γ t ht ρ
  exact hN.trans hc.symm

private theorem add_parts {ctrl : Nat → Nat} {Γ : List Ty} {σ : Ty} {i : Nat}
    {f g : OrdinalExpression (σ :: Γ)} (hg : HeadGrade ctrl Γ σ i (.add f g))
    (ha : ordinalHeadFree (.add f g) = false) : HeadGrade ctrl Γ σ i f ∧ HeadGrade ctrl Γ σ i g := by
  cases hg with
  | add hf hg => exact ⟨hf, hg⟩
  | promote hi hh hfree => simp_all

private theorem exp_parts {ctrl : Nat → Nat} {Γ : List Ty} {σ : Ty} {i : Nat}
    {f g : OrdinalExpression (σ :: Γ)} (hg : HeadGrade ctrl Γ σ i (.emul f g))
    (ha : ordinalHeadFree (.emul f g) = false) :
    HeadGrade ctrl Γ σ (i + 1) f ∧ HeadGrade ctrl Γ σ i g := by
  cases hg with
  | emul hi hf hg => exact ⟨hf, hg⟩
  | promote hi hh hfree => simp_all

private theorem collapse_parts {ctrl : Nat → Nat} {Γ : List Ty} {σ : Ty} {i : Nat}
    {f g : OrdinalExpression (σ :: Γ)} (hg : HeadGrade ctrl Γ σ i (.collapse f g))
    (ha : ordinalHeadFree (.collapse f g) = false) :
    HeadGrade ctrl Γ σ 1 f ∧ HeadGrade ctrl Γ σ 0 g := by
  cases hg with
  | collapse hf hg hn => exact ⟨hf, hg⟩
  | promote hi hh hfree => simp_all

theorem firstFreeEndpoint : SelectedFirstFreeTargets.FirstFreeEndpoint := by
  intro Γ σ i j t u hp
  induction hp <;> assumption

theorem firstFreeGrade : SelectedFirstFreeTargets.FirstFreeGrade := by
  intro ctrl Γ σ i j t u hg hp
  revert hg
  induction hp with
  | stop hf => intro hg; exact hg
  | addLeft ha hp ih => intro hg; exact ih (add_parts hg ha).1
  | addRight ha hp ih => intro hg; exact ih (add_parts hg ha).2
  | expHead hi ha hp ih => intro hg; exact ih (exp_parts hg ha).1
  | expTail hi ha hp ih => intro hg; exact ih (exp_parts hg ha).2
  | collapseHead ha hp ih => intro hg; exact ih (collapse_parts hg ha).1
  | collapseTail ha hp ih => intro hg; exact ih (collapse_parts hg ha).2

private def budget (i B : Nat) : Nat := if i = 0 then B else 2 ^ (i - 1) * B

private theorem budget_base (i B : Nat) : B ≤ budget i B := by
  by_cases hi : i = 0
  · simp [budget, hi]
  · rw [budget, if_neg hi]
    simpa using Nat.mul_le_mul_right B (Nat.one_le_pow (i - 1) 2 (by omega))

private theorem budget_step (i B : Nat) (hi : 0 < i) : budget (i + 1) B = 2 * budget i B := by
  cases i with
  | zero => omega
  | succ i => simp [budget, Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm]

private noncomputable def headNorm (ctrl : Nat → Nat) {Γ : List Ty} {σ : Ty} (ρ : AdmissibleSubstitution ctrl Γ)
    (t : OrdinalExpression (σ :: Γ)) : Nat :=
  actualOrdinalNorm (expressionValue ctrl ρ (ordinalHeadClosure t))

private theorem active_level {ctrl : Nat → Nat} {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (hg : HeadGrade ctrl Γ σ i t)
    (ha : ordinalHeadFree t = false) : i ≤ σ.level := by
  by_contra h
  have hf := SelectedSourceDomainProof.head_high_free ctrl Γ σ i t hg (by omega)
  simp [ha] at hf

private theorem budget_bound (ctrl : Nat → Nat) (K : Nat) (hctrl : SelectedWithThreshold ctrl K) {Γ : List Ty} {σ : Ty} (ρ : AdmissibleSubstitution ctrl Γ) (B : Nat)
    {i j : Nat} {t u : OrdinalExpression (σ :: Γ)} (hp : FirstFree Γ σ i t j u) :
    HeadGrade ctrl Γ σ i t → i ≤ σ.level + 1 → headNorm ctrl ρ t ≤ budget i B → 0 < j →
      headNorm ctrl ρ u ≤ 2 ^ σ.level * B := by
  induction hp with
  | @stop i t hf =>
    intro hg hi hb hj
    have hb' : headNorm ctrl ρ t ≤ 2 ^ (i - 1) * B := by simpa [budget, Nat.ne_of_gt hj] using hb
    exact hb'.trans (Nat.mul_le_mul_right B (Nat.pow_le_pow_right (by omega) (by omega)))
  | @addLeft i j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := add_parts hg ha
    have hn := (SelectedDescentNormProof.addChildNorm ctrl K hctrl Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g)
      (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ i f hf) (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ i g hgg)).1
    exact ih hf hi (hn.trans hb) hj
  | @addRight i j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := add_parts hg ha
    have hn := (SelectedDescentNormProof.addChildNorm ctrl K hctrl Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g)
      (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ i f hf) (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ i g hgg)).2
    exact ih hgg hi (hn.trans hb) hj
  | @expHead i j f g u hip ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := exp_parts hg ha
    have hlev := active_level hg ha
    have hn := (SelectedDescentNormProof.expChildNorm ctrl K hctrl Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g) hip
      (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ (i + 1) f hf) (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ i g hgg)).1
    apply ih hf (by omega) _ hj
    rw [budget_step i B hip]
    exact hn.trans (Nat.mul_le_mul_left 2 hb)
  | @expTail i j f g u hip ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := exp_parts hg ha
    have hn := (SelectedDescentNormProof.expChildNorm ctrl K hctrl Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g) hip
      (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ (i + 1) f hf) (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ i g hgg)).2
    exact ih hgg hi (hn.trans hb) hj
  | @collapseHead j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := collapse_parts hg ha
    have hn := (SelectedDescentNormProof.collapseChildNorm ctrl K hctrl Γ ρ (ordinalHeadClosure f) (ordinalHeadClosure g)
      (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 1 f hf) (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 0 g hgg)).1
    apply ih hf (by omega) _ hj
    simpa [budget, headNorm] using hn.trans hb
  | @collapseTail j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := collapse_parts hg ha
    have hn := (SelectedDescentNormProof.collapseChildNorm ctrl K hctrl Γ ρ (ordinalHeadClosure f) (ordinalHeadClosure g)
      (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 1 f hf) (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 0 g hgg)).2
    exact ih hgg hi (hn.trans hb) hj

private theorem free_path {Γ : List Ty} {σ : Ty} {i j : Nat}
    {t u : OrdinalExpression (σ :: Γ)} (hp : FirstFree Γ σ i t j u)
    (hf : ordinalHeadFree t = true) : j = i ∧ u = t := by
  cases hp <;> simp_all

theorem firstFreeBound : SelectedFirstFreeTargets.FirstFreeBound := by
  intro ctrl K hctrl Γ σ m h hg hbounded ρ i j u hp hj
  let B := finiteValue (expressionValue ctrl ρ (ordinalHeadClosure (h 0)))
  obtain ⟨ρ', hh, ho⟩ := SelectedHeadClosureProof.headOneExtension ctrl Γ σ ρ
  have hcoords : ∀ k : Fin (m + 1), headNorm ctrl ρ (h k) ≤ B := by
    intro k
    have hb := hbounded ρ' k
    rw [← SelectedHeadClosureProof.headClosureValue ctrl Γ σ ρ ρ' hh ho (h k),
      ← SelectedHeadClosureProof.headClosureValue ctrl Γ σ ρ ρ' hh ho (h 0)] at hb
    have hzero := scalar_value_norm ctrl Γ ρ (ordinalHeadClosure (h 0))
      (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 0 (h 0) (hg 0))
    rw [hzero] at hb
    exact hb
  by_cases hi : i.val ≤ σ.level + 1
  · exact budget_bound ctrl K hctrl ρ B hp (hg i) hi ((hcoords i).trans (budget_base i.val B)) hj
  · have hf := SelectedSourceDomainProof.head_high_free ctrl Γ σ i.val (h i) (hg i) (by omega)
    obtain ⟨rfl, rfl⟩ := free_path hp hf
    exact (hcoords i).trans (by
      simpa using Nat.mul_le_mul_right B (Nat.one_le_pow σ.level 2 (by omega)))

theorem fullSelectedFirstFree : SelectedFirstFreeTargets.FullSelectedFirstFree :=
  ⟨SelectedDescentNormProof.addChildNorm,SelectedDescentNormProof.expChildNorm,
    SelectedDescentNormProof.collapseChildNorm,firstFreeEndpoint,firstFreeGrade,firstFreeBound,
    fun _ _ t ht => SelectedSourceDomainProof.free_closure_reconstruct t ht,
    SelectedSupportProof.supportComparisonBridge⟩

end LogicLineages.PermittedControl.SelectedFirstFreeProof
