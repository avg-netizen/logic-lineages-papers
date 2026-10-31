module
public import LogicLineages.OrdinalComparison.WWOriginalDeltaTargets
public import LogicLineages.OrdinalComparison.WWOriginalWeakPartialProof
public import LogicLineages.OrdinalComparison.WWTypedPartialProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment

theorem originalHigherCoordinateFree : Targets.OriginalHigherCoordinateFree := by
  intro Γ σ i t h
  induction h with
  | one i => intro _; rfl
  | omega i hi => intro _; rfl
  | var x j =>
    intro hi
    cases x with
    | here => have := j.isLt; omega
    | there y => rfl
  | add hf hg ihf ihg =>
    intro hi
    have hff := ihf hi
    have hgf := ihg hi
    simp_all [ordinalHeadFree, ordinalHeadOccurs]
  | emul hi hf hg ihf ihg =>
    intro hlevel
    have hff := ihf (by omega)
    have hgf := ihg hlevel
    simp_all [ordinalHeadFree, ordinalHeadOccurs]
  | collapse hf hg hn ihf ihg => intro hi; omega
  | promote hi hh hfree ih => intro _; exact hfree

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

private theorem expand_ambient {Γ : List Ty} {n i : Nat} (s : Shape n)
    (xs : Fin n → OrdinalExpression Γ) (h : ∀ j, AmbientGrade Γ i (xs j)) :
    AmbientGrade Γ i (expand s xs) := by
  induction s with
  | leaf => exact h 0
  | @join n m a b iha ihb =>
    exact .add (iha _ (fun j => h (Fin.castAdd m j)))
      (ihb _ (fun j => h (Fin.natAdd n j)))

private theorem repeated_ambient {Γ : List Ty} {i : Nat} (p : Policy)
    (site : MacroSite) (k : Nat) (hk : 0 < k) (t : OrdinalExpression Γ)
    (ht : AmbientGrade Γ i t) : AmbientGrade Γ i (repeated p site k t) := by
  cases k with
  | zero => omega
  | succ k => exact expand_ambient _ _ (fun _ => ht)

theorem originalDeltaValid : Targets.OriginalDeltaValid := by
  intro Γ σ m p h hg
  obtain ⟨ps, hps, gps⟩ := collect_property
    (fun v : OrdinalPartialVector Γ σ => ∀ j, AmbientGrade Γ j.val (v j))
    (m + 1) (fun i => AdmissiblePartial.run p i.val (h i)) (by
      intro i
      obtain ⟨v, hv, gv, wv⟩ := originalPartialWeakAndValid Γ σ p i.val (h i) (hg i)
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
  · simp only [delta, hps, Option.bind_some]
    rfl
  · intro j
    dsimp only [v]
    split
    · rename_i hj
      rw [hj]
      exact repeated_ambient p .scalarRepeat factor hfactor _ (gps 0 0)
    · split
      · rename_i hj
        exact expand_ambient _ _ (fun i => gps i ⟨j.val, hj⟩)
      · exact originalHeadClosureGrade Γ σ j.val _ (hg ⟨j.val, by have := j.isLt; omega⟩)

theorem originalDeltaAbstractionComposition : Targets.OriginalDeltaAbstractionComposition := by
  intro Γ σ m p h v hv
  unfold delta at hv
  cases hc : collect (m + 1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hc] at hv
  | some ps =>
    simp only [hc, bind, pure, Option.bind_some, Option.some.injEq] at hv
    subst v
    simp only [abstraction, hc, bind, pure, Option.bind_some]

theorem originalSourceAbstractionValid : Targets.OriginalSourceAbstractionValid := by
  intro Γ σ m p h hg
  obtain ⟨v, hv, gv⟩ := originalDeltaValid Γ σ m p h hg
  refine ⟨_, originalDeltaAbstractionComposition Γ σ m p h v hv, ?_⟩
  intro j
  split
  · rename_i hm
    exact .add (gv j) (originalHeadClosureGrade Γ σ j.val _ (hg ⟨j.val, hm⟩))
  · exact gv j

end LogicLineages.OrdinalComparison.Source.OriginalDomain
