module
public import LogicLineages.PermittedControl.SelectedWeakPartialProof
public import LogicLineages.OrdinalComparison.WWTypedPartialProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedWeakDeltaProof
open OrdinalComparison Source SelectedSourceDomain
open Source.AdmissibleSum Source.AdmissibleAssignment

private theorem collect_property {α : Type} (P : α → Prop) (n : Nat)
    (f : Fin n → Option α) (hf : ∀ i, ∃ a, f i = some a ∧ P a) :
    ∃ v, collect n f = some v ∧ ∀ i, P (v i) := by
  induction n with
  | zero => exact ⟨Fin.elim0, rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    obtain ⟨a, ha, ga⟩ := hf 0
    obtain ⟨v, hv, gv⟩ := ih (fun i => f i.succ) (fun i => hf i.succ)
    refine ⟨Fin.cases a v, ?_, ?_⟩
    · simp [collect, ha, hv]
    · intro i
      exact Fin.cases ga gv i

private theorem expand_ambient (ctrl : Nat → Nat) {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade ctrl Γ i (xs j)) :
    AmbientGrade ctrl Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

private theorem repeated_ambient (ctrl : Nat → Nat) {Γ : List Ty} {i : Nat} (p : Policy)
    (site : MacroSite) (k : Nat) (hk : 0 < k) (t : OrdinalExpression Γ)
    (ht : AmbientGrade ctrl Γ i t) : AmbientGrade ctrl Γ i (repeated p site k t) := by
  cases k with
  | zero => omega
  | succ k => exact expand_ambient ctrl _ _ (fun _ => ht)

theorem deltaValid (ctrl : Nat → Nat) (B : Nat) (hctrl : SelectedWithThreshold ctrl B)
    (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m)
    (hg : ∀ i, HeadGrade ctrl Γ σ i.val (h i)) :
    ∃ v, LiteralCovariance.delta p h = some v ∧ ∀ j, AmbientGrade ctrl Γ j.val (v j) := by
  obtain ⟨ps, hps, gps⟩ := collect_property
    (fun v : OrdinalPartialVector Γ σ => ∀ j, AmbientGrade ctrl Γ j.val (v j))
    (m + 1) (fun i => AdmissiblePartial.run p i.val (h i)) (by
      intro i
      obtain ⟨v, hv, gv, wv⟩ := SelectedWeakPartialProof.partialWeakAndValid ctrl B hctrl Γ σ p i.val (h i) (hg i)
      exact ⟨v, hv, gv⟩)
  let factor := 2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum
  have hsum : 0 < ((List.ofFn h).map ordinalPartialSize).sum := by
    rw [List.ofFn_succ, List.map_cons, List.sum_cons]
    have := (actualTypedPartialSize Γ σ (h 0)).1
    omega
  have hfactor : 0 < factor := Nat.mul_pos (Nat.pow_pos (by omega)) hsum
  let v : OrdinalVector Γ (max (σ.level + 1) m) := fun j =>
    if j.val = 0 then repeated p .scalarRepeat factor (ps 0 0)
    else if hj : j.val < σ.level + 2 then
      expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
    else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)
  refine ⟨v, ?_, ?_⟩
  · simp only [LiteralCovariance.delta, hps, Option.bind_some]
    rfl
  · intro j
    dsimp only [v]
    split
    · rename_i hj
      rw [hj]
      exact repeated_ambient ctrl p .scalarRepeat factor hfactor _ (gps 0 0)
    · split
      · rename_i hj
        exact expand_ambient ctrl _ _ (fun i => gps i ⟨j.val, hj⟩)
      · exact SelectedHeadClosureProof.headClosureGrade ctrl Γ σ j.val _ (hg ⟨j.val, by have := j.isLt; omega⟩)

end LogicLineages.PermittedControl.SelectedWeakDeltaProof
