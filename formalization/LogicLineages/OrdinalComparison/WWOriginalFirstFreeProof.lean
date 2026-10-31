module
public import LogicLineages.OrdinalComparison.WWOriginalFirstFreeTargets
public import LogicLineages.OrdinalComparison.WWOriginalDescentNormProof
public import LogicLineages.OrdinalComparison.WWOriginalDeltaProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain

private theorem add_parts {Γ : List Ty} {σ : Ty} {i : Nat}
    {f g : OrdinalExpression (σ :: Γ)} (hg : HeadGrade Γ σ i (.add f g))
    (ha : ordinalHeadFree (.add f g) = false) : HeadGrade Γ σ i f ∧ HeadGrade Γ σ i g := by
  cases hg with
  | add hf hg => exact ⟨hf, hg⟩
  | promote hi hh hfree => simp_all

private theorem exp_parts {Γ : List Ty} {σ : Ty} {i : Nat}
    {f g : OrdinalExpression (σ :: Γ)} (hg : HeadGrade Γ σ i (.emul f g))
    (ha : ordinalHeadFree (.emul f g) = false) :
    HeadGrade Γ σ (i + 1) f ∧ HeadGrade Γ σ i g := by
  cases hg with
  | emul hi hf hg => exact ⟨hf, hg⟩
  | promote hi hh hfree => simp_all

private theorem collapse_parts {Γ : List Ty} {σ : Ty} {i : Nat}
    {f g : OrdinalExpression (σ :: Γ)} (hg : HeadGrade Γ σ i (.collapse f g))
    (ha : ordinalHeadFree (.collapse f g) = false) :
    HeadGrade Γ σ 1 f ∧ HeadGrade Γ σ 0 g := by
  cases hg with
  | collapse hf hg hn => exact ⟨hf, hg⟩
  | promote hi hh hfree => simp_all

theorem originalFirstFreeEndpoint : Targets.OriginalFirstFreeEndpoint := by
  intro Γ σ i j t u hp
  induction hp <;> assumption

theorem originalFirstFreeGrade : Targets.OriginalFirstFreeGrade := by
  intro Γ σ i j t u hg hp
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

private noncomputable def headNorm {Γ : List Ty} {σ : Ty} (ρ : AdmissibleSubstitution Γ)
    (t : OrdinalExpression (σ :: Γ)) : Nat :=
  actualOrdinalNorm (expressionValue ρ (ordinalHeadClosure t))

private theorem active_level {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (hg : HeadGrade Γ σ i t)
    (ha : ordinalHeadFree t = false) : i ≤ σ.level := by
  by_contra h
  have hf := originalHigherCoordinateFree Γ σ i t hg (by omega)
  simp [ha] at hf

private theorem budget_bound {Γ : List Ty} {σ : Ty} (ρ : AdmissibleSubstitution Γ) (B : Nat)
    {i j : Nat} {t u : OrdinalExpression (σ :: Γ)} (hp : FirstFree Γ σ i t j u) :
    HeadGrade Γ σ i t → i ≤ σ.level + 1 → headNorm ρ t ≤ budget i B → 0 < j →
      headNorm ρ u ≤ 2 ^ σ.level * B := by
  induction hp with
  | @stop i t hf =>
    intro hg hi hb hj
    have hb' : headNorm ρ t ≤ 2 ^ (i - 1) * B := by simpa [budget, Nat.ne_of_gt hj] using hb
    exact hb'.trans (Nat.mul_le_mul_right B (Nat.pow_le_pow_right (by omega) (by omega)))
  | @addLeft i j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := add_parts hg ha
    have hn := (originalAddChildNorm Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g)
      (originalHeadClosureGrade Γ σ i f hf) (originalHeadClosureGrade Γ σ i g hgg)).1
    exact ih hf hi (hn.trans hb) hj
  | @addRight i j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := add_parts hg ha
    have hn := (originalAddChildNorm Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g)
      (originalHeadClosureGrade Γ σ i f hf) (originalHeadClosureGrade Γ σ i g hgg)).2
    exact ih hgg hi (hn.trans hb) hj
  | @expHead i j f g u hip ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := exp_parts hg ha
    have hlev := active_level hg ha
    have hn := (originalExpChildNorm Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g) hip
      (originalHeadClosureGrade Γ σ (i + 1) f hf) (originalHeadClosureGrade Γ σ i g hgg)).1
    apply ih hf (by omega) _ hj
    rw [budget_step i B hip]
    exact hn.trans (Nat.mul_le_mul_left 2 hb)
  | @expTail i j f g u hip ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := exp_parts hg ha
    have hn := (originalExpChildNorm Γ ρ i (ordinalHeadClosure f) (ordinalHeadClosure g) hip
      (originalHeadClosureGrade Γ σ (i + 1) f hf) (originalHeadClosureGrade Γ σ i g hgg)).2
    exact ih hgg hi (hn.trans hb) hj
  | @collapseHead j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := collapse_parts hg ha
    have hn := (originalCollapseChildNorm Γ ρ (ordinalHeadClosure f) (ordinalHeadClosure g)
      (originalHeadClosureGrade Γ σ 1 f hf) (originalHeadClosureGrade Γ σ 0 g hgg)).1
    apply ih hf (by omega) _ hj
    simpa [budget, headNorm] using hn.trans hb
  | @collapseTail j f g u ha hp ih =>
    intro hg hi hb hj
    obtain ⟨hf, hgg⟩ := collapse_parts hg ha
    have hn := (originalCollapseChildNorm Γ ρ (ordinalHeadClosure f) (ordinalHeadClosure g)
      (originalHeadClosureGrade Γ σ 1 f hf) (originalHeadClosureGrade Γ σ 0 g hgg)).2
    exact ih hgg hi (hn.trans hb) hj

private theorem free_path {Γ : List Ty} {σ : Ty} {i j : Nat}
    {t u : OrdinalExpression (σ :: Γ)} (hp : FirstFree Γ σ i t j u)
    (hf : ordinalHeadFree t = true) : j = i ∧ u = t := by
  cases hp <;> simp_all

theorem originalFirstFreeBound : Targets.OriginalFirstFreeBound := by
  intro Γ σ m h hg hbounded ρ i j u hp hj
  let B := finiteValue (expressionValue ρ (ordinalHeadClosure (h 0)))
  obtain ⟨ρ', hh, ho⟩ := originalHeadOneExtension Γ σ ρ
  have hcoords : ∀ k : Fin (m + 1), headNorm ρ (h k) ≤ B := by
    intro k
    have hb := hbounded ρ' k
    rw [← originalHeadClosureValue Γ σ ρ ρ' hh ho (h k),
      ← originalHeadClosureValue Γ σ ρ ρ' hh ho (h 0)] at hb
    have hzero := originalScalarValueNorm Γ ρ (ordinalHeadClosure (h 0))
      (originalHeadClosureGrade Γ σ 0 (h 0) (hg 0))
    rw [hzero] at hb
    exact hb
  by_cases hi : i.val ≤ σ.level + 1
  · exact budget_bound ρ B hp (hg i) hi ((hcoords i).trans (budget_base i.val B)) hj
  · have hf := originalHigherCoordinateFree Γ σ i.val (h i) (hg i) (by omega)
    obtain ⟨rfl, rfl⟩ := free_path hp hf
    exact (hcoords i).trans (by
      simpa using Nat.mul_le_mul_right B (Nat.one_le_pow σ.level 2 (by omega)))

end LogicLineages.OrdinalComparison.Source.OriginalDomain
