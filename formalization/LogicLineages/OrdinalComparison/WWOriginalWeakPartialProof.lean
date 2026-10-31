module
public import LogicLineages.OrdinalComparison.WWOriginalWeakPartialTargets
public import LogicLineages.OrdinalComparison.WWOriginalHeadClosureProof
public import LogicLineages.OrdinalComparison.WWOriginalValueClosureProof
public import LogicLineages.OrdinalComparison.WWFiniteNaturalTailProof
public import LogicLineages.OrdinalComparison.WWAdmissibleSumProof
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem expand_ambient {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade Γ i (xs j)) :
    AmbientGrade Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

private theorem three_ambient {Γ : List Ty} {i : Nat} (p : Policy) (site : MacroSite)
    {a b c : OrdinalExpression Γ} (ha : AmbientGrade Γ i a)
    (hb : AmbientGrade Γ i b) (hc : AmbientGrade Γ i c) :
    AmbientGrade Γ i (three p site a b c) := by
  apply expand_ambient
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

private theorem twice_ambient {Γ : List Ty} {i : Nat} (p : Policy)
    {a : OrdinalExpression Γ} (ha : AmbientGrade Γ i a) :
    AmbientGrade Γ i (twice p a) := expand_ambient _ _ (fun _ => ha)

private theorem three_value {Γ : List Ty} (p : Policy) (site : MacroSite)
    (a b c : OrdinalExpression Γ) (ρ : AdmissibleSubstitution Γ) :
    expressionValue ρ (three p site a b c) = ordinalNaturalSum
      (ordinalNaturalSum (expressionValue ρ a) (expressionValue ρ b)) (expressionValue ρ c) := by
  exact actualAdmissibleSumValue Γ 3 (p.shape site 2)
    (.join (.join .leaf .leaf) .leaf)
    (fun j => if j.val = 0 then a else if j.val = 1 then b else c) (valuation ρ)

private theorem scalar_control_mono {Γ : List Ty} {a b : OrdinalExpression Γ}
    (ha : AmbientGrade Γ 0 a) (hb : AmbientGrade Γ 0 b)
    (ρ : AdmissibleSubstitution Γ) (hle : expressionValue ρ a ≤ expressionValue ρ b) :
    fastControl 2 (finiteValue (expressionValue ρ a)) ≤
      fastControl 2 (finiteValue (expressionValue ρ b)) := by
  obtain ⟨r, hr⟩ := originalAmbientScalarFinite Γ a ha ρ
  obtain ⟨s, hs⟩ := originalAmbientScalarFinite Γ b hb ρ
  rw [hr, hs] at hle ⊢
  rw [originalFiniteValueCalibration, originalFiniteValueCalibration]
  exact (fastControl_strictMono 2).monotone (by exact_mod_cast hle)

private theorem collapse_head_below {Γ : List Ty} (f : OrdinalExpression Γ)
    (ρ : AdmissibleSubstitution Γ) :
    ordinalNaturalProduct Ordinal.omega0 (expressionValue ρ f) < epsilonZero := by
  have hf := originalExpressionValueBelowEpsilonZero Γ ρ f
  have hω : Ordinal.omega0 < epsilonZero := originalClosedValueBelowEpsilonZero .omega
  obtain ⟨x, hx⟩ := normalRepresentationComplete Ordinal.omega0 hω
  obtain ⟨y, hy⟩ := normalRepresentationComplete (expressionValue ρ f) hf
  rw [← hx, ← hy, ← naturalProductDenotation x y]
  exact normalRepresentationSound (naturalProduct x y)

private theorem free_partial {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (p : Policy) (hg : HeadGrade Γ σ i t)
    (hf : ordinalHeadFree t = true) : ∃ v : OrdinalPartialVector Γ σ,
      run p i t = some v ∧ (∀ j, AmbientGrade Γ j.val (v j)) ∧
      (i = 0 → ∀ ρ : AdmissibleSubstitution Γ,
        expressionValue ρ (ordinalHeadClosure t) ≤ expressionValue ρ (v 0)) := by
  refine ⟨ordinalFreePartialVector i t, by rw [run.eq_def, hf]; rfl, ?_, ?_⟩
  · intro j
    unfold ordinalFreePartialVector
    split
    · rename_i hij
      rw [← hij]
      exact .add (originalHeadClosureGrade Γ σ i t hg) (.one i)
    · exact .one j.val
  · intro hi ρ
    subst i
    change expressionValue ρ (ordinalHeadClosure t) ≤
      ordinalNaturalSum (expressionValue ρ (ordinalHeadClosure t)) 1
    have h := actualNaturalSumFiniteRight (expressionValue ρ (ordinalHeadClosure t)) 1
    simp only [Nat.cast_one] at h
    rw [h]
    exact le_self_add

theorem originalPartialWeakAndValid : Targets.OriginalPartialWeakAndValid := by
  intro Γ σ p i t h
  induction h with
  | one i => exact free_partial p (.one i) rfl
  | omega i hi => exact free_partial p (.omega i hi) rfl
  | var x k =>
    cases x with
    | here =>
      refine ⟨fun _ => .one, ?_, fun j => .one j.val, ?_⟩
      · simp [run, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
      · intro hk ρ
        exact le_rfl
    | there x => exact free_partial p (.var (.there x) k) rfl
  | @add i f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.add f g) = true
    · exact free_partial p (.add hf hg) hfree
    · obtain ⟨pf, hpf, gpf, wpf⟩ := ihf
      obtain ⟨pg, hpg, gpg, wpg⟩ := ihg
      refine ⟨fun j => three p .activeAdd (pf j) (pg j) .one, ?_, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, hpf, hpg]
        rfl
      · intro j
        exact three_ambient p .activeAdd (gpf j) (gpg j) (.one j.val)
      · intro hi ρ
        subst i
        obtain ⟨a, ha⟩ := originalAmbientScalarFinite Γ _ (originalHeadClosureGrade Γ σ 0 f hf) ρ
        obtain ⟨b, hb⟩ := originalAmbientScalarFinite Γ _ (originalHeadClosureGrade Γ σ 0 g hg) ρ
        obtain ⟨c, hc⟩ := originalAmbientScalarFinite Γ _ (gpf 0) ρ
        obtain ⟨d, hd⟩ := originalAmbientScalarFinite Γ _ (gpg 0) ρ
        have hac := wpf rfl ρ
        have hbd := wpg rfl ρ
        rw [ha, hc] at hac
        rw [hb, hd] at hbd
        have hac' : a ≤ c := by exact_mod_cast hac
        have hbd' : b ≤ d := by exact_mod_cast hbd
        change ordinalNaturalSum (expressionValue ρ (ordinalHeadClosure f))
          (expressionValue ρ (ordinalHeadClosure g)) ≤
          expressionValue ρ (three p .activeAdd (pf 0) (pg 0) .one)
        rw [three_value, ha, hb, hc, hd, naturalSum_finite, naturalSum_finite]
        change ((a + b : Nat) : Ordinal) ≤ ordinalNaturalSum ((c + d : Nat) : Ordinal) 1
        have he := naturalSum_finite (c + d) 1
        simp only [Nat.cast_one] at he
        rw [he]
        exact_mod_cast (show a + b ≤ c + d + 1 by omega)
  | @emul i f g hi hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.emul f g) = true
    · exact free_partial p (.emul hi hf hg) hfree
    · obtain ⟨pf, hpf, gpf, wpf⟩ := ihf
      obtain ⟨pg, hpg, gpg, wpg⟩ := ihg
      refine ⟨fun j => three p .activeExp (twice p (pf j)) (pg j) .one, ?_, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, if_pos hi, hpf, hpg]
        rfl
      · intro j
        exact three_ambient p .activeExp (twice_ambient p (gpf j)) (gpg j) (.one j.val)
      · intro he
        omega
  | @collapse f g hf hg hn ihf ihg =>
    by_cases hfree : ordinalHeadFree (.collapse f g) = true
    · exact free_partial p (.collapse hf hg hn) hfree
    · obtain ⟨pf, hpf, gpf, wpf⟩ := ihf
      obtain ⟨pg, hpg, gpg, wpg⟩ := ihg
      have hfc := originalHeadClosureGrade Γ σ 1 f hf
      have hgc := originalHeadClosureGrade Γ σ 0 g hg
      have hnc : CollapseNormPremise (ordinalHeadClosure f) (pg 0) := by
        intro ρ
        exact (originalHeadClosureNormPremise Γ σ f g hn ρ).trans
          (scalar_control_mono hgc (gpg 0) ρ (wpg rfl ρ))
      refine ⟨fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j), ?_, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, if_pos rfl, hpf, hpg]
        rfl
      · intro j
        dsimp only
        split
        · rename_i hj
          rw [hj]
          exact .collapse hfc (gpg 0) hnc
        · exact .add (gpf j) (gpg j)
      · intro _ ρ
        obtain ⟨r, hr⟩ := originalAmbientScalarFinite Γ _ hgc ρ
        obtain ⟨s, hs⟩ := originalAmbientScalarFinite Γ _ (gpg 0) ρ
        have hrs := wpg rfl ρ
        rw [hr, hs] at hrs
        have hrs' : r ≤ s := by exact_mod_cast hrs
        change (actualCollapse (ordinalNaturalSum
          (ordinalNaturalProduct Ordinal.omega0 (expressionValue ρ (ordinalHeadClosure f)))
          (expressionValue ρ (ordinalHeadClosure g))) : Ordinal) ≤
          (actualCollapse (ordinalNaturalSum
          (ordinalNaturalProduct Ordinal.omega0 (expressionValue ρ (ordinalHeadClosure f)))
          (expressionValue ρ (pg 0))) : Ordinal)
        rw [hr, hs]
        exact_mod_cast actualCollapseNaturalFiniteTailMonotone _
          (collapse_head_below (ordinalHeadClosure f) ρ) r s hrs'
  | promote hi hh hfree ih => exact free_partial p (.promote hi hh hfree) hfree

end LogicLineages.OrdinalComparison.Source.OriginalDomain
