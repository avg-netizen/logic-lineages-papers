module
public import LogicLineages.OrdinalComparison.WWSourceMacroProfileTargets
public import LogicLineages.OrdinalComparison.WWSourceProfileProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceClasses
open AdmissibleSum AdmissiblePartial AdmissibleAssignment

theorem repeated_noOmega {Γ : List Ty} (p : Policy) (site : MacroSite) (k : Nat)
    (t : OrdinalExpression Γ) (ht : noOmega t = true) : noOmega (repeated p site k t) = true := by
  cases k with
  | zero => rfl
  | succ k => exact expand_noOmega _ _ (fun _ => ht)

theorem repeated_height {Γ : List Ty} (p : Policy) (site : MacroSite) (k : Nat)
    (t : OrdinalExpression Γ) (K : Nat) (ht : headHeight t ≤ K) :
    headHeight (repeated p site k t) ≤ K := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => exact expand_height _ _ K (fun _ => ht)

private theorem tail_noOmega {Γ : List Ty} (p : Policy) (n : Nat) (f g : OrdinalExpression Γ)
    (hf : noOmega f = true) (hg : noOmega g = true) : noOmega (boxTail p n f g) = true := by
  unfold boxTail
  split
  · simp [noOmega, hf, hg]
  · exact three_noOmega p .optionalBoxTail hf hg (repeated_noOmega p .numeral n .one rfl)

private theorem tail_height {Γ : List Ty} (p : Policy) (n K : Nat) (f g : OrdinalExpression Γ)
    (hf : headHeight f ≤ K) (hg : headHeight g ≤ K) : headHeight (boxTail p n f g) ≤ K := by
  unfold boxTail
  split
  · exact max_le hf hg
  · exact three_height p .optionalBoxTail K hf hg (repeated_height p .numeral n .one K (Nat.zero_le _))

private theorem at_noOmega {Γ : List Ty} {m : Nat} (f : OrdinalVector Γ m)
    (hf : ∀ j, noOmega (f j) = true) (i : Nat) : noOmega (ordinalVectorAt f i) = true := by
  unfold ordinalVectorAt
  split
  · exact hf _
  · rfl

private theorem positive_noOmega {Γ : List Ty} (n : Nat) (f g : Nat → OrdinalExpression Γ)
    (hf : ∀ i, noOmega (f i) = true) (hg : ∀ i, noOmega (g i) = true) (i : Nat) :
    noOmega (ordinalBoxPositive n f g i) = true := by
  rw [ordinalBoxPositive]
  split
  · have hi := positive_noOmega n f g hf hg (i + 1)
    simp only [noOmega, hi, hf i, hg i]
    rfl
  · exact hf i
termination_by n + 1 - i
decreasing_by omega

theorem sourceBoxNoOmega : Targets.SourceBoxNoOmega := by
  intro Γ m n p f g hf hg j
  have hpos := positive_noOmega n (ordinalVectorAt f) (ordinalVectorAt g)
    (at_noOmega f hf) (at_noOmega g hg)
  rw [box]
  split
  · simp only [noOmega, hpos 1, tail_noOmega p n (f 0) (g 0) (hf 0) (hg 0)]
    rfl
  · exact hpos j.val

private theorem positive_height {Γ : List Ty} {L m n : Nat} (hnm : n < m) (hmL : m ≤ L)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n)
    (hf : ∀ j, headHeight (f j) ≤ L - j.val) (hg : ∀ j, headHeight (g j) ≤ L - j.val)
    (i : Nat) (hi : 0 < i) (him : i ≤ m) :
    headHeight (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) i) ≤ L - i := by
  rw [ordinalBoxPositive]
  split
  · rename_i hin
    have hh := positive_height hnm hmL f g hf hg (i + 1) (by omega) (by omega)
    apply max_le
    · omega
    · apply max_le
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
      · simpa only [ordinalVectorAt, dif_pos (by omega : i < n + 1)] using hg ⟨i, by omega⟩
  · simpa only [ordinalVectorAt, dif_pos (by omega : i < m + 1)] using hf ⟨i, by omega⟩
termination_by n + 1 - i
decreasing_by omega

theorem sourceBoxHeadHeight : Targets.SourceBoxHeadHeight := by
  intro Γ L m n hnm hmL p f g hf hg j
  rw [box]
  split
  · rename_i hj
    simp only [headHeight, hj, Nat.sub_zero]
    apply max_le
    · have hh := positive_height hnm hmL f g hf hg 1 (by omega) (by omega)
      omega
    · exact tail_height p n L (f 0) (g 0) (hf 0) (hg 0)
  · rename_i hj
    exact positive_height hnm hmL f g hf hg j.val (by omega) (by have := j.isLt; omega)

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

theorem sourceAbstractionNoOmega : Targets.SourceAbstractionNoOmega := by
  intro Γ σ m p h v hv hh
  unfold abstraction at hv
  cases hps : collect (m + 1) (fun i => run p i.val (h i)) with
  | none => simp [hps] at hv
  | some ps =>
    simp only [hps, bind, pure, Option.bind_some, Option.some.injEq] at hv
    have hspec := collect_success _ _ ps hps
    have gp : ∀ i j, noOmega (ps i j) = true :=
      fun i => sourcePartialNoOmega Γ σ p i.val (h i) (ps i) (hspec i) (hh i)
    let F := 2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum
    let D : OrdinalVector Γ (max (σ.level + 1) m) := fun j =>
      if j.val = 0 then repeated p .scalarRepeat F (ps 0 0)
      else if hj : j.val < σ.level + 2 then
        expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
      else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)
    have hv' : (fun j : Fin (max (σ.level + 1) m + 1) => if hm : j.val < m + 1 then
        .add (D j) (ordinalHeadClosure (h ⟨j.val, hm⟩)) else D j) = v := hv
    subst v
    have hD : ∀ j, noOmega (D j) = true := by
      intro j
      dsimp only [D]
      split
      · exact repeated_noOmega p .scalarRepeat F (ps 0 0) (gp 0 0)
      · split
        · exact expand_noOmega _ _ (fun i => gp i _)
        · rw [(sourceHeadClosureProfile Γ σ _).1]
          exact hh _
    intro j
    dsimp only
    split
    · change (noOmega (D j) && noOmega (ordinalHeadClosure _)) = true
      rw [hD j, (sourceHeadClosureProfile Γ σ _).1, hh _]
      rfl
    · exact hD j

theorem sourceAbstractionHeadHeight : Targets.SourceAbstractionHeadHeight := by
  intro Γ σ L m p h v hv hh
  unfold abstraction at hv
  cases hps : collect (m + 1) (fun i => run p i.val (h i)) with
  | none => simp [hps] at hv
  | some ps =>
    simp only [hps, bind, pure, Option.bind_some, Option.some.injEq] at hv
    have hspec := collect_success _ _ ps hps
    have gp : ∀ i j, headHeight (ps i j) ≤ L - j.val :=
      fun i => sourcePartialHeadHeight Γ σ p L i.val (h i) (ps i) (hspec i) (hh i)
    let F := 2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum
    let D : OrdinalVector Γ (max (σ.level + 1) m) := fun j =>
      if j.val = 0 then repeated p .scalarRepeat F (ps 0 0)
      else if hj : j.val < σ.level + 2 then
        expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
      else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)
    have hv' : (fun j : Fin (max (σ.level + 1) m + 1) => if hm : j.val < m + 1 then
        .add (D j) (ordinalHeadClosure (h ⟨j.val, hm⟩)) else D j) = v := hv
    subst v
    have hD : ∀ j, headHeight (D j) ≤ L - j.val := by
      intro j
      dsimp only [D]
      split
      · rename_i hj
        simpa only [hj, Nat.sub_zero] using repeated_height p .scalarRepeat F (ps 0 0) L (gp 0 0)
      · split
        · exact expand_height _ _ _ (fun i => gp i _)
        · rw [(sourceHeadClosureProfile Γ σ _).2]
          exact hh _
    intro j
    dsimp only
    split
    · change max (headHeight (D j)) (headHeight (ordinalHeadClosure _)) ≤ _
      rw [(sourceHeadClosureProfile Γ σ _).2]
      exact max_le (hD j) (hh _)
    · exact hD j

end LogicLineages.OrdinalComparison.Source.SourceClasses
