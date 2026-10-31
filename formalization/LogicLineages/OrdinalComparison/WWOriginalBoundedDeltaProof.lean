module
public import LogicLineages.OrdinalComparison.WWOriginalBoundedDeltaTargets
public import LogicLineages.OrdinalComparison.WWOriginalPartialNormProof
public import LogicLineages.OrdinalComparison.WWOriginalSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment

theorem originalBoundedVectorSupportBridge : Targets.OriginalBoundedVectorSupportBridge := by
  intro Γ m h
  constructor
  · intro hb j
    have hs := originalComparisonSupportCoverage Γ (h j) (h 0)
    exact (originalSupportComparisonBridge Γ _ _ _ hs.1 hs.2
      (fun a b => actualOrdinalNorm a ≤ actualOrdinalNorm b)).mp (fun ρ => hb ρ j)
  · intro hb ρ j
    have hs := originalComparisonSupportCoverage Γ (h j) (h 0)
    exact (originalSupportComparisonBridge Γ _ _ _ hs.1 hs.2
      (fun a b => actualOrdinalNorm a ≤ actualOrdinalNorm b)).mpr (hb j) ρ

private theorem collect_success {α : Type} (n : Nat) (f : Fin n → Option α)
    (v : Fin n → α) (hv : collect n f = some v) : ∀ i, f i = some (v i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    have he : ∃ a, f 0 = some a ∧ ∃ w,
        collect n (fun i => f i.succ) = some w ∧ Fin.cases a w = v := by
      simpa only [collect, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hv
    obtain ⟨a, ha, w, hw, rfl⟩ := he
    intro i
    exact Fin.cases ha (ih _ w hw) i

private theorem ofFn_sum_le (n : Nat) (f g : Fin n → Nat) (h : ∀ i, f i ≤ g i) :
    (List.ofFn f).sum ≤ (List.ofFn g).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons]
    exact Nat.add_le_add (h 0) (ih _ _ (fun i => h i.succ))

private theorem ofFn_mul_sum (n : Nat) (f : Fin n → Nat) (K : Nat) :
    (List.ofFn (fun i => f i * K)).sum = (List.ofFn f).sum * K := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.sum_cons]
    rw [ih, Nat.add_mul]

theorem originalDeltaPreservesBoundedNorm : Targets.OriginalDeltaPreservesBoundedNorm := by
  intro Γ σ m p h hg hsource
  have hb := (originalBoundedVectorSupportBridge (σ :: Γ) m h).mpr hsource
  obtain ⟨v, hv, gv⟩ := originalDeltaValid Γ σ m p h hg
  refine ⟨v, hv, gv, (originalBoundedVectorSupportBridge Γ _ v).mp ?_⟩
  intro ρ j
  by_cases hj0 : j.val = 0
  · have hj : j = 0 := Fin.ext hj0
    subst j
    exact le_rfl
  · have hjpos : 0 < j.val := by omega
    unfold delta at hv
    cases hps : collect (m + 1) (fun i => AdmissiblePartial.run p i.val (h i)) with
    | none => simp [hps] at hv
    | some ps =>
      simp only [hps, bind, pure, Option.bind_some, Option.some.injEq] at hv
      have hspec := collect_success _ _ ps hps
      let S := ((List.ofFn h).map ordinalPartialSize).sum
      let F := 2 ^ (σ.level + 1) * S
      let D : OrdinalVector Γ (max (σ.level + 1) m) := fun k =>
        if k.val = 0 then repeated p .scalarRepeat F (ps 0 0)
        else if hk : k.val < σ.level + 2 then
          expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨k.val, hk⟩)
        else ordinalHeadClosure (h ⟨k.val, by have := k.isLt; omega⟩)
      have hrepr : D = v := hv
      have hS : 0 < S := by
        dsimp only [S]
        rw [List.ofFn_succ, List.map_cons, List.sum_cons]
        have := (actualTypedPartialSize Γ σ (h 0)).1
        omega
      have hF : 0 < F := Nat.mul_pos (Nat.pow_pos (by omega)) hS
      obtain ⟨q, hq, gq, wq⟩ := originalPartialWeakAndValid Γ σ p 0 (h 0) (hg 0)
      have heq : q = ps 0 := Option.some.inj (hq.symm.trans (hspec 0))
      subst q
      let H := finiteValue (expressionValue ρ (ps 0 0))
      let B := finiteValue (expressionValue ρ (ordinalHeadClosure (h 0)))
      have hBH : B ≤ H := by
        obtain ⟨b, hbval⟩ := originalAmbientScalarFinite Γ _
          (originalHeadClosureGrade Γ σ 0 (h 0) (hg 0)) ρ
        obtain ⟨a, haval⟩ := originalAmbientScalarFinite Γ _ (gq 0) ρ
        have hw := wq rfl ρ
        rw [hbval, haval] at hw
        dsimp only [B, H]
        rw [hbval, haval, originalFiniteValueCalibration, originalFiniteValueCalibration]
        exact_mod_cast hw
      have hHbig : H ≤ F * H := by
        simpa using Nat.mul_le_mul_right H (show 1 ≤ F by omega)
      have hn0 : actualOrdinalNorm (expressionValue ρ (repeated p .scalarRepeat F (ps 0 0))) = F * H := by
        rw [originalPositiveRepeatNorm Γ ρ p .scalarRepeat F _ hF,
          originalScalarValueNorm Γ ρ _ (gq 0)]
      obtain ⟨ρ', hh, ho⟩ := originalHeadOneExtension Γ σ ρ
      have hcoords : ∀ k : Fin (m + 1),
          actualOrdinalNorm (expressionValue ρ (ordinalHeadClosure (h k))) ≤ B := by
        intro k
        have hc := hb ρ' k
        rw [← originalHeadClosureValue Γ σ ρ ρ' hh ho (h k),
          ← originalHeadClosureValue Γ σ ρ ρ' hh ho (h 0)] at hc
        rw [originalScalarValueNorm Γ ρ _ (originalHeadClosureGrade Γ σ 0 (h 0) (hg 0))] at hc
        exact hc
      rw [← hrepr]
      change actualOrdinalNorm (expressionValue ρ (D j)) ≤
        actualOrdinalNorm (expressionValue ρ (repeated p .scalarRepeat F (ps 0 0)))
      rw [hn0]
      by_cases hj : j.val < σ.level + 2
      · simp only [D, if_neg hj0, dif_pos hj]
        rw [originalShapeNormAdditivity, List.map_ofFn]
        change (List.ofFn (fun i : Fin (m + 1) =>
          actualOrdinalNorm (expressionValue ρ (ps i ⟨j.val, hj⟩)))).sum ≤ F * H
        let K := 2 ^ (σ.level + 1) * H
        calc
          _ ≤ (List.ofFn (fun i : Fin (m + 1) => ordinalPartialSize (h i) * K)).sum :=
            ofFn_sum_le _ _ _ (fun i => originalVectorPartialNorm Γ σ m p h hg hb ρ
              (ps 0) (hspec 0) i (ps i) (hspec i) ⟨j.val, hj⟩ hjpos)
          _ = (List.ofFn (fun i : Fin (m + 1) => ordinalPartialSize (h i))).sum * K := ofFn_mul_sum _ _ _
          _ = F * H := by
            dsimp only [F, S, K]
            rw [List.map_ofFn]
            simp only [Function.comp_def]
            ac_rfl
      · simp only [D, if_neg hj0, dif_neg hj]
        exact (hcoords ⟨j.val, by have := j.isLt; omega⟩).trans (hBH.trans hHbig)

end LogicLineages.OrdinalComparison.Source.OriginalDomain
