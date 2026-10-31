module
public import LogicLineages.OrdinalComparison.WWSourceProfileTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open AdmissibleSum AdmissiblePartial
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

private theorem and_true_iff (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> decide

theorem sourceHeadClosureProfile : Targets.SourceHeadClosureProfile := by
  intro Γ σ t
  induction t with
  | var c =>
    rcases c with ⟨τ, x, j⟩
    cases x <;> exact ⟨rfl, rfl⟩
  | zero => exact ⟨rfl, rfl⟩
  | one => exact ⟨rfl, rfl⟩
  | omega => exact ⟨rfl, rfl⟩
  | add f g ihf ihg =>
    constructor
    · change (noOmega (ordinalHeadClosure f) && noOmega (ordinalHeadClosure g)) = (noOmega f && noOmega g)
      rw [ihf.1, ihg.1]
    · change max (headHeight (ordinalHeadClosure f)) (headHeight (ordinalHeadClosure g)) = max (headHeight f) (headHeight g)
      rw [ihf.2, ihg.2]
  | emul f g ihf ihg =>
    constructor
    · change (noOmega (ordinalHeadClosure f) && noOmega (ordinalHeadClosure g)) = (noOmega f && noOmega g)
      rw [ihf.1, ihg.1]
    · change max (headHeight (ordinalHeadClosure f) + 1) (headHeight (ordinalHeadClosure g)) = max (headHeight f + 1) (headHeight g)
      rw [ihf.2, ihg.2]
  | collapse f g ihf ihg =>
    constructor
    · change (noOmega (ordinalHeadClosure f) && noOmega (ordinalHeadClosure g)) = (noOmega f && noOmega g)
      rw [ihf.1, ihg.1]
    · change max (headHeight (ordinalHeadClosure f) + 1) (headHeight (ordinalHeadClosure g)) = max (headHeight f + 1) (headHeight g)
      rw [ihf.2, ihg.2]

theorem expand_noOmega {Γ : List Ty} {n : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, noOmega (xs j) = true) :
    noOmega (expand s xs) = true := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact (and_true_iff _ _).mpr ⟨iha _ (fun j => h (Fin.castAdd m j)),
      ihb _ (fun j => h (Fin.natAdd n j))⟩

theorem expand_height {Γ : List Ty} {n : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (K : Nat) (h : ∀ j, headHeight (xs j) ≤ K) :
    headHeight (expand s xs) ≤ K := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact max_le (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

theorem three_noOmega {Γ : List Ty} (p : Policy) (site : MacroSite)
    {a b c : OrdinalExpression Γ} (ha : noOmega a = true) (hb : noOmega b = true)
    (hc : noOmega c = true) : noOmega (three p site a b c) = true := by
  apply expand_noOmega
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

theorem three_height {Γ : List Ty} (p : Policy) (site : MacroSite)
    {a b c : OrdinalExpression Γ} (K : Nat) (ha : headHeight a ≤ K) (hb : headHeight b ≤ K)
    (hc : headHeight c ≤ K) : headHeight (three p site a b c) ≤ K := by
  apply expand_height
  intro j
  split
  · exact ha
  · split
    · exact hb
    · exact hc

theorem twice_noOmega {Γ : List Ty} (p : Policy) {a : OrdinalExpression Γ}
    (ha : noOmega a = true) : noOmega (twice p a) = true := expand_noOmega _ _ (fun _ => ha)

theorem twice_height {Γ : List Ty} (p : Policy) {a : OrdinalExpression Γ} (K : Nat)
    (ha : headHeight a ≤ K) : headHeight (twice p a) ≤ K := expand_height _ _ K (fun _ => ha)

private theorem free_noOmega {Γ : List Ty} {σ : Ty} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (hf : ordinalHeadFree t = true)
    (v : OrdinalPartialVector Γ σ) (hv : run p i t = some v) (hn : noOmega t = true) :
    ∀ j, noOmega (v j) = true := by
  rw [run.eq_def, hf] at hv
  have he : ordinalFreePartialVector i t = v := Option.some.inj hv
  subst v
  intro j
  unfold ordinalFreePartialVector
  split
  · simp only [noOmega, (sourceHeadClosureProfile Γ σ t).1, hn, Bool.and_true]
  · rfl

private theorem free_height {Γ : List Ty} {σ : Ty} (p : Policy) (L i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (hf : ordinalHeadFree t = true)
    (v : OrdinalPartialVector Γ σ) (hv : run p i t = some v) (ht : headHeight t ≤ L - i) :
    ∀ j, headHeight (v j) ≤ L - j.val := by
  rw [run.eq_def, hf] at hv
  have he : ordinalFreePartialVector i t = v := Option.some.inj hv
  subst v
  intro j
  unfold ordinalFreePartialVector
  split
  · rename_i hij
    simp only [headHeight, (sourceHeadClosureProfile Γ σ t).2, Nat.max_zero]
    simpa only [← hij] using ht
  · exact Nat.zero_le _

theorem sourcePartialNoOmega : Targets.SourcePartialNoOmega := by
  intro Γ σ p i t v hv ht
  induction t generalizing i v with
  | zero => exact free_noOmega p i .zero rfl v hv ht
  | one => exact free_noOmega p i .one rfl v hv ht
  | omega => exact free_noOmega p i .omega rfl v hv ht
  | var c =>
    by_cases hf : ordinalHeadFree (.var c) = true
    · exact free_noOmega p i (.var c) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      simp only [Bool.false_eq_true, if_false] at hv
      split at hv
      · have he : (fun _ => .one) = v := Option.some.inj hv
        subst v
        intro j
        rfl
      · contradiction
  | add f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact free_noOmega p i (.add f g) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      have hex : ∃ pf : OrdinalPartialVector Γ σ, run p (i) f = some pf ∧
          ∃ pg : OrdinalPartialVector Γ σ, run p (i) g = some pg ∧
          (fun j => three p .activeAdd (pf j) (pg j) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure,
          Option.bind_eq_some_iff, Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, he⟩ := hex
      subst v
      have hp : noOmega f = true ∧ noOmega g = true := (and_true_iff _ _).mp ht
      have hpf' := ihf (i) pf hpf hp.1
      have hpg' := ihg (i) pg hpg hp.2
      intro j
      exact three_noOmega p .activeAdd (hpf' j) (hpg' j) rfl
  | emul f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact free_noOmega p i (.emul f g) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : 0 < i
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ, run p (i + 1) f = some pf ∧
            ∃ pg : OrdinalPartialVector Γ σ, run p (i) g = some pg ∧
            (fun j => three p .activeExp (twice p (pf j)) (pg j) .one) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, he⟩ := hex
        subst v
        have hp : noOmega f = true ∧ noOmega g = true := (and_true_iff _ _).mp ht
        have hpf' := ihf (i + 1) pf hpf hp.1
        have hpg' := ihg (i) pg hpg hp.2
        intro j
        exact three_noOmega p .activeExp (twice_noOmega p (hpf' j)) (hpg' j) rfl
      · simp [hi] at hv
  | collapse f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact free_noOmega p i (.collapse f g) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : i = 0
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ, run p (1) f = some pf ∧
            ∃ pg : OrdinalPartialVector Γ σ, run p (0) g = some pg ∧
            (fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0) else .add (pf j) (pg j)) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, he⟩ := hex
        subst v
        have hp : noOmega f = true ∧ noOmega g = true := (and_true_iff _ _).mp ht
        have hpf' := ihf (1) pf hpf hp.1
        have hpg' := ihg (0) pg hpg hp.2
        intro j
        dsimp only
        split
        · exact (and_true_iff _ _).mpr ⟨by rw [(sourceHeadClosureProfile Γ σ f).1]; exact hp.1, hpg' 0⟩
        · exact (and_true_iff _ _).mpr ⟨hpf' j, hpg' j⟩
      · simp [hi] at hv

theorem sourcePartialHeadHeight : Targets.SourcePartialHeadHeight := by
  intro Γ σ p L i t v hv ht
  induction t generalizing i v with
  | zero => exact free_height p L i .zero rfl v hv ht
  | one => exact free_height p L i .one rfl v hv ht
  | omega => exact free_height p L i .omega rfl v hv ht
  | var c =>
    by_cases hf : ordinalHeadFree (.var c) = true
    · exact free_height p L i (.var c) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      simp only [Bool.false_eq_true, if_false] at hv
      split at hv
      · have he : (fun _ => .one) = v := Option.some.inj hv
        subst v
        intro j
        exact Nat.zero_le _
      · contradiction
  | add f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.add f g) = true
    · exact free_height p L i (.add f g) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      have hex : ∃ pf : OrdinalPartialVector Γ σ, run p (i) f = some pf ∧
          ∃ pg : OrdinalPartialVector Γ σ, run p (i) g = some pg ∧
          (fun j => three p .activeAdd (pf j) (pg j) .one) = v := by
        simpa only [Bool.false_eq_true, if_false, bind, pure,
          Option.bind_eq_some_iff, Option.some.injEq] using hv
      obtain ⟨pf, hpf, pg, hpg, he⟩ := hex
      subst v
      have hp : headHeight f ≤ L - i ∧ headHeight g ≤ L - i := max_le_iff.mp ht
      have hpf' := ihf (i) pf hpf (by exact hp.1)
      have hpg' := ihg (i) pg hpg (by exact hp.2)
      intro j
      exact three_height p .activeAdd _ (hpf' j) (hpg' j) (Nat.zero_le _)
  | emul f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.emul f g) = true
    · exact free_height p L i (.emul f g) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : 0 < i
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ, run p (i + 1) f = some pf ∧
            ∃ pg : OrdinalPartialVector Γ σ, run p (i) g = some pg ∧
            (fun j => three p .activeExp (twice p (pf j)) (pg j) .one) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, he⟩ := hex
        subst v
        have hp : headHeight f + 1 ≤ L - i ∧ headHeight g ≤ L - i := max_le_iff.mp ht
        have hpf' := ihf (i + 1) pf hpf (by omega)
        have hpg' := ihg (i) pg hpg (by exact hp.2)
        intro j
        exact three_height p .activeExp _ (twice_height p _ (hpf' j)) (hpg' j) (Nat.zero_le _)
      · simp [hi] at hv
  | collapse f g ihf ihg =>
    by_cases hf : ordinalHeadFree (.collapse f g) = true
    · exact free_height p L i (.collapse f g) hf v hv ht
    · rw [run, Bool.eq_false_iff.mpr hf] at hv
      by_cases hi : i = 0
      · rw [if_pos hi] at hv
        have hex : ∃ pf : OrdinalPartialVector Γ σ, run p (1) f = some pf ∧
            ∃ pg : OrdinalPartialVector Γ σ, run p (0) g = some pg ∧
            (fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0) else .add (pf j) (pg j)) = v := by
          simpa only [Bool.false_eq_true, if_false, bind, pure,
            Option.bind_eq_some_iff, Option.some.injEq] using hv
        obtain ⟨pf, hpf, pg, hpg, he⟩ := hex
        subst v
        have hp : headHeight f + 1 ≤ L - i ∧ headHeight g ≤ L - i := max_le_iff.mp ht
        have hpf' := ihf (1) pf hpf (by omega)
        have hpg' := ihg (0) pg hpg (by omega)
        intro j
        dsimp only
        split
        · rename_i hj
          simp only [headHeight, (sourceHeadClosureProfile Γ σ f).2, hj, Nat.sub_zero]
          exact max_le (by omega) (by simpa using hpg' 0)
        · exact max_le (hpf' j) (hpg' j)
      · simp [hi] at hv

end LogicLineages.OrdinalComparison.Source.SourceClasses
