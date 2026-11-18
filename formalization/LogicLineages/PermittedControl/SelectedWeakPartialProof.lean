module
public import LogicLineages.PermittedControl.SelectedSumValueProof
public import LogicLineages.PermittedControl.SelectedHeadClosureProof
public import LogicLineages.PermittedControl.SelectedGradedPositivityProof
public import LogicLineages.OrdinalComparison.Control

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedWeakPartialProof
open OrdinalComparison Source SelectedSourceDomain
open Source.AdmissibleSum Source.AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem ambient_scalar_finite (ctrl : Nat → Nat) (Γ : List Ty)
    (t : OrdinalExpression Γ) (h : AmbientGrade ctrl Γ 0 t)
    (ρ : AdmissibleSubstitution ctrl Γ) : ∃ n : Nat, expressionValue ctrl ρ t = (n : Ordinal.{0}) :=
  SourceScalarCalibrationProof.ambient_scalar_finite ctrl h ρ rfl

private theorem finite_calibration (n : Nat) : finiteValue (n : Ordinal.{0}) = n :=
  (SourceScalarCalibrationProof.natural_calibration n).1

private theorem finite_tail_mono (ctrl : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold ctrl B)
    (a : Ordinal.{0}) (ha : a < epsilonZero) (r s : Nat) (hrs : r ≤ s) :
    ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum a (r : Ordinal)) ≤
      ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum a (s : Ordinal)) := by
  rw [actualNaturalSumFiniteRight,actualNaturalSumFiniteRight]
  have hs : a + (s : Ordinal.{0}) = (a + (r : Ordinal)) + ((s-r : Nat) : Ordinal) := by
    rw [add_assoc,← Nat.cast_add,Nat.add_sub_of_le hrs]
  have h := (selectedCollapseEstimates ctrl (SelectedGradedPositivityProof.selected_forms hf)).2.2.2.1
    (a + (r : Ordinal)) (s-r) (actualFiniteTailClosureNorm a ha r).1
  rw [← hs] at h
  exact (Nat.le_add_right _ _).trans h

private theorem expand_ambient (ctrl : Nat → Nat) {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade ctrl Γ i (xs j)) :
    AmbientGrade ctrl Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

private theorem three_ambient (ctrl : Nat → Nat) {Γ : List Ty} {i : Nat} (p : Policy) (site : MacroSite)
    {a b c : OrdinalExpression Γ} (ha : AmbientGrade ctrl Γ i a)
    (hb : AmbientGrade ctrl Γ i b) (hc : AmbientGrade ctrl Γ i c) :
    AmbientGrade ctrl Γ i (three p site a b c) := by
  apply expand_ambient ctrl
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

private theorem twice_ambient (ctrl : Nat → Nat) {Γ : List Ty} {i : Nat} (p : Policy)
    {a : OrdinalExpression Γ} (ha : AmbientGrade ctrl Γ i a) :
    AmbientGrade ctrl Γ i (twice p a) := expand_ambient ctrl _ _ (fun _ => ha)

private theorem three_value (ctrl : Nat → Nat) {Γ : List Ty} (p : Policy) (site : MacroSite)
    (a b c : OrdinalExpression Γ) (ρ : AdmissibleSubstitution ctrl Γ) :
    expressionValue ctrl ρ (three p site a b c) = ordinalNaturalSum
      (ordinalNaturalSum (expressionValue ctrl ρ a) (expressionValue ctrl ρ b)) (expressionValue ctrl ρ c) := by
  exact SelectedSumValueProof.sum_value ctrl Γ 3 (p.shape site 2)
    (.join (.join .leaf .leaf) .leaf)
    (fun j => if j.val = 0 then a else if j.val = 1 then b else c) (valuation ctrl ρ)

private theorem scalar_control_mono (ctrl : Nat → Nat) {Γ : List Ty} {a b : OrdinalExpression Γ}
    (ha : AmbientGrade ctrl Γ 0 a) (hb : AmbientGrade ctrl Γ 0 b)
    (ρ : AdmissibleSubstitution ctrl Γ) (hle : expressionValue ctrl ρ a ≤ expressionValue ctrl ρ b) :
    fastControl 2 (finiteValue (expressionValue ctrl ρ a)) ≤
      fastControl 2 (finiteValue (expressionValue ctrl ρ b)) := by
  obtain ⟨r, hr⟩ := ambient_scalar_finite ctrl Γ a ha ρ
  obtain ⟨s, hs⟩ := ambient_scalar_finite ctrl Γ b hb ρ
  rw [hr, hs] at hle ⊢
  rw [finite_calibration, finite_calibration]
  exact (fastControl_strictMono 2).monotone (by exact_mod_cast hle)

private theorem collapse_head_below (ctrl : Nat → Nat) {Γ : List Ty} (f : OrdinalExpression Γ)
    (ρ : AdmissibleSubstitution ctrl Γ) :
    ordinalNaturalProduct Ordinal.omega0 (expressionValue ctrl ρ f) < epsilonZero := by
  have hf := SelectedValueClosureProof.ambient_below ctrl ρ f
  have hω : Ordinal.omega0 < epsilonZero := SelectedValueClosureProof.omega_below
  obtain ⟨x, hx⟩ := normalRepresentationComplete Ordinal.omega0 hω
  obtain ⟨y, hy⟩ := normalRepresentationComplete (expressionValue ctrl ρ f) hf
  rw [← hx, ← hy, ← naturalProductDenotation x y]
  exact normalRepresentationSound (naturalProduct x y)

private theorem free_partial (ctrl : Nat → Nat) {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (p : Policy) (hg : HeadGrade ctrl Γ σ i t)
    (hf : ordinalHeadFree t = true) : ∃ v : OrdinalPartialVector Γ σ,
      run p i t = some v ∧ (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧
      (i = 0 → ∀ ρ : AdmissibleSubstitution ctrl Γ,
        expressionValue ctrl ρ (ordinalHeadClosure t) ≤ expressionValue ctrl ρ (v 0)) := by
  refine ⟨ordinalFreePartialVector i t, by rw [run.eq_def, hf]; rfl, ?_, ?_⟩
  · intro j
    unfold ordinalFreePartialVector
    split
    · rename_i hij
      rw [← hij]
      exact .add (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ i t hg) (.one i)
    · exact .one j.val
  · intro hi ρ
    subst i
    change expressionValue ctrl ρ (ordinalHeadClosure t) ≤
      ordinalNaturalSum (expressionValue ctrl ρ (ordinalHeadClosure t)) 1
    have h := actualNaturalSumFiniteRight (expressionValue ctrl ρ (ordinalHeadClosure t)) 1
    simp only [Nat.cast_one] at h
    rw [h]
    exact le_self_add

theorem partialWeakAndValid : SelectedWeakScalarTargets.PartialWeakAndValid := by
  intro ctrl B hctrl Γ σ p i t h
  induction h with
  | one i => exact free_partial ctrl p (.one i) rfl
  | omega i hi => exact free_partial ctrl p (.omega i hi) rfl
  | var x k =>
    cases x with
    | here =>
      refine ⟨fun _ => .one, ?_, fun j => .one j.val, ?_⟩
      · simp [run, ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
      · intro hk ρ
        exact le_rfl
    | there x => exact free_partial ctrl p (.var (.there x) k) rfl
  | @add i f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.add f g) = true
    · exact free_partial ctrl p (.add hf hg) hfree
    · obtain ⟨pf, hpf, gpf, wpf⟩ := ihf
      obtain ⟨pg, hpg, gpg, wpg⟩ := ihg
      refine ⟨fun j => three p .activeAdd (pf j) (pg j) .one, ?_, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, hpf, hpg]
        rfl
      · intro j
        exact three_ambient ctrl p .activeAdd (gpf j) (gpg j) (.one j.val)
      · intro hi ρ
        subst i
        obtain ⟨a, ha⟩ := ambient_scalar_finite ctrl Γ _ (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 0 f hf) ρ
        obtain ⟨b, hb⟩ := ambient_scalar_finite ctrl Γ _ (SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 0 g hg) ρ
        obtain ⟨c, hc⟩ := ambient_scalar_finite ctrl Γ _ (gpf 0) ρ
        obtain ⟨d, hd⟩ := ambient_scalar_finite ctrl Γ _ (gpg 0) ρ
        have hac := wpf rfl ρ
        have hbd := wpg rfl ρ
        rw [ha, hc] at hac
        rw [hb, hd] at hbd
        have hac' : a ≤ c := by exact_mod_cast hac
        have hbd' : b ≤ d := by exact_mod_cast hbd
        change ordinalNaturalSum (expressionValue ctrl ρ (ordinalHeadClosure f))
          (expressionValue ctrl ρ (ordinalHeadClosure g)) ≤
          expressionValue ctrl ρ (three p .activeAdd (pf 0) (pg 0) .one)
        rw [three_value ctrl, ha, hb, hc, hd, naturalSum_finite, naturalSum_finite]
        change ((a + b : Nat) : Ordinal) ≤ ordinalNaturalSum ((c + d : Nat) : Ordinal) 1
        have he := naturalSum_finite (c + d) 1
        simp only [Nat.cast_one] at he
        rw [he]
        exact_mod_cast (show a + b ≤ c + d + 1 by omega)
  | @emul i f g hi hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.emul f g) = true
    · exact free_partial ctrl p (.emul hi hf hg) hfree
    · obtain ⟨pf, hpf, gpf, wpf⟩ := ihf
      obtain ⟨pg, hpg, gpg, wpg⟩ := ihg
      refine ⟨fun j => three p .activeExp (twice p (pf j)) (pg j) .one, ?_, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, if_pos hi, hpf, hpg]
        rfl
      · intro j
        exact three_ambient ctrl p .activeExp (twice_ambient ctrl p (gpf j)) (gpg j) (.one j.val)
      · intro he
        omega
  | @collapse f g hf hg hn ihf ihg =>
    by_cases hfree : ordinalHeadFree (.collapse f g) = true
    · exact free_partial ctrl p (.collapse hf hg hn) hfree
    · obtain ⟨pf, hpf, gpf, wpf⟩ := ihf
      obtain ⟨pg, hpg, gpg, wpg⟩ := ihg
      have hfc := SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 1 f hf
      have hgc := SelectedHeadClosureProof.headClosureGrade ctrl Γ σ 0 g hg
      have hnc : CollapseNormPremise ctrl (ordinalHeadClosure f) (pg 0) := by
        intro ρ
        exact (SelectedHeadClosureProof.headClosureNormPremise ctrl Γ σ f g hn ρ).trans
          (scalar_control_mono ctrl hgc (gpg 0) ρ (wpg rfl ρ))
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
        obtain ⟨r, hr⟩ := ambient_scalar_finite ctrl Γ _ hgc ρ
        obtain ⟨s, hs⟩ := ambient_scalar_finite ctrl Γ _ (gpg 0) ρ
        have hrs := wpg rfl ρ
        rw [hr, hs] at hrs
        have hrs' : r ≤ s := by exact_mod_cast hrs
        change (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
          (ordinalNaturalProduct Ordinal.omega0 (expressionValue ctrl ρ (ordinalHeadClosure f)))
          (expressionValue ctrl ρ (ordinalHeadClosure g))) : Ordinal) ≤
          (ParametricActualCollapse.collapseWith ctrl (ordinalNaturalSum
          (ordinalNaturalProduct Ordinal.omega0 (expressionValue ctrl ρ (ordinalHeadClosure f)))
          (expressionValue ctrl ρ (pg 0))) : Ordinal)
        rw [hr, hs]
        exact_mod_cast finite_tail_mono ctrl B hctrl _
          (collapse_head_below ctrl (ordinalHeadClosure f) ρ) r s hrs'
  | promote hi hh hfree ih => exact free_partial ctrl p (.promote hi hh hfree) hfree

end LogicLineages.PermittedControl.SelectedWeakPartialProof
