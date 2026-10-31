module
public import LogicLineages.OrdinalComparison.WWAdmissiblePartialTargets
public import LogicLineages.OrdinalComparison.WWAdmissibleSumProof
public import LogicLineages.OrdinalComparison.WWGeneratedGradeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissiblePartial
open AdmissibleSum
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem three_generated {Γ : List Ty} {i : Nat} (p : Policy) (site : MacroSite)
    {a b c : OrdinalExpression Γ} (ha : GeneratedOrdinalGrade Γ i a)
    (hb : GeneratedOrdinalGrade Γ i b) (hc : GeneratedOrdinalGrade Γ i c) :
    GeneratedOrdinalGrade Γ i (three p site a b c) := by
  apply expand_generated
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

private theorem twice_generated {Γ : List Ty} {i : Nat} (p : Policy)
    {a : OrdinalExpression Γ} (ha : GeneratedOrdinalGrade Γ i a) :
    GeneratedOrdinalGrade Γ i (twice p a) :=
  expand_generated _ _ (fun _ => ha)

private theorem free_admissible_partial_graded {Γ : List Ty} {σ : Ty} {i : Nat}
    {t : OrdinalExpression (σ :: Γ)} (policy : Policy) (hg : GeneratedOrdinalGrade (σ :: Γ) i t)
    (hf : ordinalHeadFree t = true) : ∃ v : OrdinalPartialVector Γ σ,
      run policy i t = some v ∧ ∀ j, GeneratedOrdinalGrade Γ j.val (v j) := by
  refine ⟨ordinalFreePartialVector i t, by rw [run.eq_def, hf]; rfl, ?_⟩
  intro j
  unfold ordinalFreePartialVector
  split
  · rename_i hij
    rw [← hij]
    exact .add (actualGeneratedGradeHeadClosure Γ σ i t hg) (.one i)
  · exact .one j.val

theorem actualAdmissiblePartialGenerated : Targets.ActualAdmissiblePartialGenerated := by
  intro Γ σ policy i t h
  induction h with
  | one i => exact free_admissible_partial_graded policy (.one i) rfl
  | omega i hi => exact free_admissible_partial_graded policy (.omega i hi) rfl
  | var v k =>
    cases v with
    | here =>
      refine ⟨fun _ => .one, ?_, fun j => .one j.val⟩
      rw [run]
      simp [ordinalHeadFree, ordinalHeadOccurs, ordinalHeadComponentOccurs]
    | there v => exact free_admissible_partial_graded policy (.var (.there v) k) rfl
  | @add i f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.add f g) = true
    · exact free_admissible_partial_graded policy (.add hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => three policy .activeAdd (pf j) (pg j) .one, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, hpf, hpg]
        rfl
      · intro j
        exact three_generated policy .activeAdd (gpf j) (gpg j) (.one j.val)
  | @emul i f g hi hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.emul f g) = true
    · exact free_admissible_partial_graded policy (.emul hi hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => three policy .activeExp (twice policy (pf j)) (pg j) .one, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, if_pos hi,
          hpf, hpg]
        rfl
      · intro j
        exact three_generated policy .activeExp (twice_generated policy (gpf j))
          (gpg j) (.one j.val)
  | @collapse f g hf hg ihf ihg =>
    by_cases hfree : ordinalHeadFree (.collapse f g) = true
    · exact free_admissible_partial_graded policy (.collapse hf hg) hfree
    · obtain ⟨pf, hpf, gpf⟩ := ihf
      obtain ⟨pg, hpg, gpg⟩ := ihg
      refine ⟨fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j), ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hfree, if_pos rfl,
          hpf, hpg]
        rfl
      · intro j
        dsimp only
        split
        · rename_i hj
          rw [hj]
          exact .collapse (actualGeneratedGradeHeadClosure Γ σ 1 f hf) (gpg 0)
        · exact .add (gpf j) (gpg j)



private theorem three_value {Γ : List Ty} (p q : Policy) (site : MacroSite)
    (a b c a' b' c' : OrdinalExpression Γ) (ρ : OrdinalComponent Γ → Ordinal)
    (ha : denote ρ a = denote ρ a') (hb : denote ρ b = denote ρ b')
    (hc : denote ρ c = denote ρ c') :
    denote ρ (three p site a b c) = denote ρ (three q site a' b' c') := by
  apply expand_value_congr
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

private theorem twice_value {Γ : List Ty} (p q : Policy)
    (a b : OrdinalExpression Γ) (ρ : OrdinalComponent Γ → Ordinal)
    (h : denote ρ a = denote ρ b) :
    denote ρ (twice p a) = denote ρ (twice q b) :=
  expand_value_congr _ _ _ _ ρ (fun _ => h)

private theorem free_input_values {Γ : List Ty} {σ : Ty} (p q : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (hf : ordinalHeadFree t = true)
    (v : OrdinalPartialVector Γ σ) (hv : run p i t = some v) :
    ∃ w, run q i t = some w ∧
      ∀ (j : Fin (σ.level + 2)) (ρ : OrdinalComponent Γ → Ordinal),
        denote ρ (v j) = denote ρ (w j) := by
  rw [run.eq_def, hf] at hv
  have hv' : ordinalFreePartialVector i t = v := Option.some.inj hv
  subst v
  refine ⟨ordinalFreePartialVector i t, ?_, fun _ _ => rfl⟩
  rw [run.eq_def, hf]
  rfl

theorem actualAdmissiblePartialValue : Targets.ActualAdmissiblePartialValue := by
  intro Γ σ p q i t
  induction t generalizing i with
  | zero => intro v hv; exact free_input_values p q i .zero rfl v hv
  | one => intro v hv; exact free_input_values p q i .one rfl v hv
  | omega => intro v hv; exact free_input_values p q i .omega rfl v hv
  | var c =>
    intro v hv
    by_cases hf : ordinalHeadFree (.var c) = true
    · exact free_input_values p q i (.var c) hf v hv
    · refine ⟨v, ?_, fun _ _ => rfl⟩
      simpa only [run] using hv
  | add f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact free_input_values p q i (.add f g) hf v hv
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      have hex : ∃ pf : OrdinalPartialVector Γ σ,
          run p i f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
          run p i g = some pg ∧
          (fun j => three p .activeAdd (pf j) (pg j) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure,
          Option.bind_eq_some_iff, Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
      subst v
      obtain ⟨qf, hqf, eqf⟩ := ihf i pf hpf
      obtain ⟨qg, hqg, eqg⟩ := ihg i pg hpg
      refine ⟨fun j => three q .activeAdd (qf j) (qg j) .one, ?_, ?_⟩
      · rw [run, Bool.eq_false_iff.mpr hf, hqf, hqg]
        rfl
      · intro j ρ
        exact three_value p q .activeAdd _ _ _ _ _ _ ρ (eqf j ρ) (eqg j ρ) rfl
  | emul f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact free_input_values p q i (.emul f g) hf v hv
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : 0 < i
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ,
            run p (i + 1) f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            run p i g = some pg ∧
            (fun j => three p .activeExp (twice p (pf j)) (pg j) .one) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
        subst v
        obtain ⟨qf, hqf, eqf⟩ := ihf (i + 1) pf hpf
        obtain ⟨qg, hqg, eqg⟩ := ihg i pg hpg
        refine ⟨fun j => three q .activeExp (twice q (qf j)) (qg j) .one, ?_, ?_⟩
        · rw [run, Bool.eq_false_iff.mpr hf, if_pos hi, hqf, hqg]
          rfl
        · intro j ρ
          exact three_value p q .activeExp _ _ _ _ _ _ ρ
            (twice_value p q _ _ ρ (eqf j ρ)) (eqg j ρ) rfl
      · simp [hi] at hv
  | collapse f g ihf ihg =>
    intro v hv
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact free_input_values p q i (.collapse f g) hf v hv
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : i = 0
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ,
            run p 1 f = some pf ∧ ∃ pg : OrdinalPartialVector Γ σ,
            run p 0 g = some pg ∧
            (fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
              else .add (pf j) (pg j)) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, hv⟩ := hex
        subst v
        obtain ⟨qf, hqf, eqf⟩ := ihf 1 pf hpf
        obtain ⟨qg, hqg, eqg⟩ := ihg 0 pg hpg
        refine ⟨fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (qg 0)
          else .add (qf j) (qg j), ?_, ?_⟩
        · rw [run, Bool.eq_false_iff.mpr hf, if_pos hi, hqf, hqg]
          rfl
        · intro j ρ
          by_cases hj : j.val = 0
          · simp only [if_pos hj, denote, eqg 0 ρ]
          · simp only [if_neg hj, denote, eqf j ρ, eqg j ρ]
      · simp [hi] at hv

end LogicLineages.OrdinalComparison.Source.AdmissiblePartial
