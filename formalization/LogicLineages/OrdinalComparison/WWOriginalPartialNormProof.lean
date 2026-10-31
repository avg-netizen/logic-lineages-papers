module
public import LogicLineages.OrdinalComparison.WWOriginalPartialNormTargets
public import LogicLineages.OrdinalComparison.WWOriginalFirstFreeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem one_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) :
    actualOrdinalNorm (expressionValue ρ .one) = 1 := by
  simpa [expressionValue, denote] using (finiteNorm 1).2

private theorem add_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) (f g : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ρ (.add f g)) =
      actualOrdinalNorm (expressionValue ρ f) + actualOrdinalNorm (expressionValue ρ g) :=
  actualNaturalSumNormAdditivity _ _ (originalExpressionValueBelowEpsilonZero Γ ρ f)
    (originalExpressionValueBelowEpsilonZero Γ ρ g)

private theorem three_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) (p : Policy)
    (site : MacroSite) (a b c : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ρ (three p site a b c)) =
      actualOrdinalNorm (expressionValue ρ a) + actualOrdinalNorm (expressionValue ρ b) +
        actualOrdinalNorm (expressionValue ρ c) := by
  unfold three
  rw [originalShapeNormAdditivity]
  simp [List.ofFn_succ, Nat.add_assoc]

private theorem twice_norm {Γ : List Ty} (ρ : AdmissibleSubstitution Γ) (p : Policy)
    (a : OrdinalExpression Γ) :
    actualOrdinalNorm (expressionValue ρ (twice p a)) = 2 * actualOrdinalNorm (expressionValue ρ a) := by
  unfold twice
  rw [originalShapeNormAdditivity]
  simp [List.ofFn_succ, Nat.two_mul]

private theorem free_norm {Γ : List Ty} {σ : Ty} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (hf : ordinalHeadFree t = true)
    (ρ : AdmissibleSubstitution Γ) (C : Nat) (hC : 0 < C)
    (hb : ∀ k u, FirstFree Γ σ i t k u → 0 < k →
      actualOrdinalNorm (expressionValue ρ (ordinalHeadClosure u)) ≤ C)
    (v : OrdinalPartialVector Γ σ) (hv : run p i t = some v)
    (j : Fin (σ.level + 2)) (hj : 0 < j.val) :
    actualOrdinalNorm (expressionValue ρ (v j)) ≤ ordinalPartialSize t * (2 * C) := by
  rw [run.eq_def, hf] at hv
  have he : ordinalFreePartialVector i t = v := Option.some.inj hv
  subst v
  have hs : ordinalPartialSize t = 1 := by rw [ordinalPartialSize.eq_def, hf]; rfl
  rw [hs, Nat.one_mul]
  unfold ordinalFreePartialVector
  split
  · rename_i hij
    have hn := hb i t (.stop hf) (by omega)
    rw [add_norm, one_norm]
    omega
  · rw [one_norm]
    omega

theorem originalPartialNormFromFreeBudget : Targets.OriginalPartialNormFromFreeBudget := by
  intro Γ σ p i t hg
  induction hg with
  | one i => intro ρ C hC hb v hv j hj; exact free_norm p i .one rfl ρ C hC hb v hv j hj
  | omega i hi => intro ρ C hC hb v hv j hj; exact free_norm p i .omega rfl ρ C hC hb v hv j hj
  | var x k =>
    intro ρ C hC hb v hv j hj
    cases x with
    | there x => exact free_norm p k.val _ rfl ρ C hC hb v hv j hj
    | here =>
      have he : (fun _ : Fin (σ.level + 2) => (.one : OrdinalExpression Γ)) = v := by
        simpa [run, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs] using hv
      rw [← he, one_norm]
      have hs : ordinalPartialSize (.var ⟨σ, Variable.here, k⟩ : OrdinalExpression (σ :: Γ)) = 1 := rfl
      rw [hs, Nat.one_mul]
      omega
  | @add i f g hf hg ihf ihg =>
    intro ρ C hC hb v hv j hj
    by_cases hfree : ordinalHeadFree (.add f g) = true
    · exact free_norm p i _ hfree ρ C hC hb v hv j hj
    · have ha := Bool.eq_false_iff.mpr hfree
      rw [run, ha] at hv
      have he : ∃ pf : OrdinalPartialVector Γ σ, run p i f = some pf ∧
          ∃ pg : OrdinalPartialVector Γ σ, run p i g = some pg ∧
          (fun k => three p .activeAdd (pf k) (pg k) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, he⟩ := he
      subst v
      have bf := ihf ρ C hC (fun k u hp hk => hb k u (.addLeft ha hp) hk) pf hpf j hj
      have bg := ihg ρ C hC (fun k u hp hk => hb k u (.addRight ha hp) hk) pg hpg j hj
      rw [three_norm, one_norm, ordinalPartialSize, ha]
      simp only [Bool.false_eq_true, if_false, Nat.add_mul, Nat.one_mul]
      omega
  | @emul i f g hi hf hg ihf ihg =>
    intro ρ C hC hb v hv j hj
    by_cases hfree : ordinalHeadFree (.emul f g) = true
    · exact free_norm p i _ hfree ρ C hC hb v hv j hj
    · have ha := Bool.eq_false_iff.mpr hfree
      rw [run, ha, if_pos hi] at hv
      have he : ∃ pf : OrdinalPartialVector Γ σ, run p (i + 1) f = some pf ∧
          ∃ pg : OrdinalPartialVector Γ σ, run p i g = some pg ∧
          (fun k => three p .activeExp (twice p (pf k)) (pg k) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, he⟩ := he
      subst v
      have bf := ihf ρ C hC (fun k u hp hk => hb k u (.expHead hi ha hp) hk) pf hpf j hj
      have bg := ihg ρ C hC (fun k u hp hk => hb k u (.expTail hi ha hp) hk) pg hpg j hj
      rw [three_norm, twice_norm, one_norm, ordinalPartialSize, ha]
      simp only [Bool.false_eq_true, if_false, Nat.add_mul, Nat.one_mul, Nat.mul_assoc]
      omega
  | @collapse f g hf hg hn ihf ihg =>
    intro ρ C hC hb v hv j hj
    by_cases hfree : ordinalHeadFree (.collapse f g) = true
    · exact free_norm p 0 _ hfree ρ C hC hb v hv j hj
    · have ha := Bool.eq_false_iff.mpr hfree
      rw [run, ha, if_pos rfl] at hv
      have he : ∃ pf : OrdinalPartialVector Γ σ, run p 1 f = some pf ∧
          ∃ pg : OrdinalPartialVector Γ σ, run p 0 g = some pg ∧
          (fun k => if k.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
            else .add (pf k) (pg k)) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure, Option.bind_eq_some_iff,
          Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, he⟩ := he
      subst v
      have bf := ihf ρ C hC (fun k u hp hk => hb k u (.collapseHead ha hp) hk) pf hpf j hj
      have bg := ihg ρ C hC (fun k u hp hk => hb k u (.collapseTail ha hp) hk) pg hpg j hj
      simp only [if_neg (Nat.ne_of_gt hj)]
      rw [add_norm, ordinalPartialSize, ha]
      simp only [Bool.false_eq_true, if_false, Nat.add_mul, Nat.one_mul]
      omega
  | promote hi hh hfree ih =>
    intro ρ C hC hb v hv j hj
    exact free_norm p _ _ hfree ρ C hC hb v hv j hj

theorem originalVectorPartialNorm : Targets.OriginalVectorPartialNorm := by
  intro Γ σ m p h hg hb ρ w hw i v hv j hj
  obtain ⟨w', hw', gw, ww⟩ := originalPartialWeakAndValid Γ σ p 0 (h 0) (hg 0)
  have he : w' = w := Option.some.inj (hw'.symm.trans hw)
  subst w'
  let H := finiteValue (expressionValue ρ (w 0))
  let B := finiteValue (expressionValue ρ (ordinalHeadClosure (h 0)))
  have hH : 0 < H := by
    have := originalScalarPositiveValue Γ (w 0) (gw 0) ρ
    omega
  have hBH : B ≤ H := by
    obtain ⟨b, hbval⟩ := originalAmbientScalarFinite Γ _
      (originalHeadClosureGrade Γ σ 0 (h 0) (hg 0)) ρ
    obtain ⟨a, haval⟩ := originalAmbientScalarFinite Γ _ (gw 0) ρ
    have hweak := ww rfl ρ
    rw [hbval, haval] at hweak
    dsimp only [B, H]
    rw [hbval, haval, originalFiniteValueCalibration, originalFiniteValueCalibration]
    exact_mod_cast hweak
  have hC : 0 < 2 ^ σ.level * H := Nat.mul_pos (Nat.pow_pos (by omega)) hH
  have hfree : ∀ k u, FirstFree Γ σ i.val (h i) k u → 0 < k →
      actualOrdinalNorm (expressionValue ρ (ordinalHeadClosure u)) ≤ 2 ^ σ.level * H := by
    intro k u hp hk
    exact (originalFirstFreeBound Γ σ m h hg hb ρ i k u hp hk).trans
      (Nat.mul_le_mul_left _ hBH)
  have hbound := originalPartialNormFromFreeBudget Γ σ p i.val (h i) (hg i)
    ρ (2 ^ σ.level * H) hC hfree v hv j hj
  have hfactor : 2 * (2 ^ σ.level * H) = 2 ^ (σ.level + 1) * H := by
    rw [Nat.pow_succ]
    ac_rfl
  simpa only [hfactor] using hbound

end LogicLineages.OrdinalComparison.Source.OriginalDomain
