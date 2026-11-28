module

public import LogicLineages.NativeModule.PersistentMarking.CollapseDiagonalTargets
import LogicLineages.NativeModule.PersistentMarking.ActualCollapseCriticalProof

public section

namespace LogicLineages.PersistentMarking.CollapseDiagonalProof
open Ordinal Cardinal ConditionalTowerCofinality OrdinalRealizationTargets ActualCollapse CollapseDiagonal
open scoped Ordinal

universe u

theorem exact_DiagonalCollapse : DiagonalCollapse.{u} := by
  intro I _ D top p L Γ H fp hfix hΓ least
  have oneΓ : (1 : Ordinal.{0}) ≤ Γ.val := H.baseAboveOne.le
  have noFixedBelow : ∀ θ : CountableOrdinal, 1 ≤ θ.val → θ.val < fp.val → L θ ≠ θ := by
    intro θ h1 hθ hfixθ
    by_cases hle : θ.val ≤ Γ.val
    · exact H.noEarlyFixed θ h1 hle hfixθ
    · exact absurd (least θ (not_le.1 hle) hfixθ) (not_le.2 hθ)
  have levelBelow : ∀ e : CountableOrdinal, 1 ≤ e.val → e.val < fp.val → D.psi (p e) = (L e).val :=
    fun e h1 he => H.level e h1 (fun θ h1θ hθe => noFixedBelow θ h1θ (lt_of_le_of_lt hθe he))
  have belowFp : ∀ e : CountableOrdinal, e.val < fp.val → (L e).val < fp.val := by
    intro e he
    have := H.strict e fp he
    rwa [hfix] at this
  have stepUp : ∀ e : CountableOrdinal, 1 ≤ e.val → e.val < fp.val → e.val < (L e).val := by
    intro e h1 he
    exact lt_of_le_of_ne (H.inflationary e) (fun heq => noFixedBelow e h1 he (Subtype.ext heq.symm))
  -- the iteration of `L` from `Γ`
  let seq : ℕ → CountableOrdinal := fun n => L^[n] Γ
  have seqSucc : ∀ n, seq (n + 1) = L (seq n) := fun n => Function.iterate_succ_apply' L n Γ
  have seqFacts : ∀ n, Γ.val ≤ (seq n).val ∧ (seq n).val < fp.val := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, hΓ⟩
    | succ n ih =>
      rw [seqSucc n]
      exact ⟨ih.1.trans (H.inflationary (seq n)), belowFp (seq n) ih.2⟩
  have seqStep : ∀ n, (seq n).val < (seq (n + 1)).val := by
    intro n
    rw [seqSucc n]
    exact stepUp (seq n) (oneΓ.trans (seqFacts n).1) (seqFacts n).2
  let f : ℕ → Ordinal.{0} := fun n => (seq (n + 1)).val
  have fStrict : StrictMono f := strictMono_nat_of_lt_succ (fun n => seqStep (n + 1))
  have fCritical : ∀ n, D.critical (f n) := by
    intro n
    have eq : D.psi (p (seq n)) = (seq (n + 1)).val := by
      rw [seqSucc n]
      exact levelBelow (seq n) (oneΓ.trans (seqFacts n).1) (seqFacts n).2
    have crit := (H.characterization (p (seq n))).1
    rw [eq] at crit
    exact crit
  have bdd : BddAbove (Set.range (fun n => (seq n).val)) := Ordinal.bddAbove_range _
  let σ : Ordinal.{0} := ⨆ n, (seq n).val
  have σle : σ ≤ fp.val := Ordinal.iSup_le (fun n => (seqFacts n).2.le)
  have σlt : σ < ω₁ := lt_of_le_of_lt σle (countable_val_lt fp)
  let σc := mkCountable σ σlt
  have seqLe : ∀ n, (seq n).val ≤ σ := fun n => Ordinal.le_iSup (fun n => (seq n).val) n
  have Γσ : Γ.val < σ := lt_of_lt_of_le (seqStep 0) (seqLe 1)
  have belowσ : ∀ e : CountableOrdinal, e.val < σ → (L e).val ≤ σ := by
    intro e he
    obtain ⟨n, hn⟩ := (lt_ciSup_iff bdd).1 he
    have := (H.strict e (seq n) hn).le
    rw [← seqSucc n] at this
    exact this.trans (seqLe (n + 1))
  have σfixed : L σc = σc := by
    apply Subtype.ext
    refine le_antisymm ?_ (H.inflationary σc)
    rcases zero_or_succ_or_isSuccLimit σ with h0 | ⟨c, hc⟩ | hl
    · exact absurd (lt_of_lt_of_eq Γσ h0) not_lt_zero
    · have hcl : c < σ := by rw [← hc]; exact Order.lt_succ c
      obtain ⟨n, hn⟩ := (lt_ciSup_iff bdd).1 hcl
      have big : σ ≤ (seq n).val := by rw [← hc]; exact Order.succ_le_of_lt hn
      exact absurd (lt_of_le_of_lt big (seqStep n)) (not_lt.2 (seqLe (n + 1)))
    · exact H.limit σc hl σ belowσ
  have fpσ : fp.val = σ := le_antisymm (least σc Γσ σfixed) σle
  have lub : IsLUB (Set.range f) fp.val := by
    constructor
    · rintro _ ⟨n, rfl⟩
      exact (seqFacts (n + 1)).2.le
    · intro b hb
      rw [fpσ]
      exact Ordinal.iSup_le (fun n => (seqStep n).le.trans (hb ⟨n, rfl⟩))
  have critFp : D.critical fp.val := H.criticalSup f fStrict fCritical fp.val lub
  -- upper bound: `fp` satisfies the clause (P) at `top`
  have upper : D.psi top ≤ fp.val := by
    refine (H.characterization top).2.2 fp.val critFp (fun η hη hn => ?_)
    have mlt : max (D.norm η) Γ.val < fp.val := max_lt hn hΓ
    let e1 := mkCountable (max (D.norm η) Γ.val) (mlt.trans (countable_val_lt fp))
    have e1one : (1 : Ordinal.{0}) ≤ e1.val := oneΓ.trans (le_max_right _ _)
    let e2 := L e1
    have e12 : e1.val < e2.val := stepUp e1 e1one mlt
    have e2one : (1 : Ordinal.{0}) ≤ e2.val := e1one.trans e12.le
    have e2fp : e2.val < fp.val := belowFp e1 mlt
    have normLt : D.norm η < e2.val := lt_of_le_of_lt (le_max_left _ _) e12
    have ηlt : η < p e2 := H.cover η hη e2 e2one normLt
    have eq := levelBelow e2 e2one e2fp
    have closed := (H.characterization (p e2)).2.1 η ηlt
      (by rw [eq]; exact lt_of_lt_of_le normLt (H.inflationary e2))
    rw [eq] at closed
    exact closed.trans (belowFp e2 e2fp)
  -- lower bound: a smaller value would be a fixed point of `L` below `fp`
  refine le_antisymm upper (not_lt.1 (fun hlt => ?_))
  have δcrit := (H.characterization top).1
  have δone : (1 : Ordinal.{0}) < D.psi top :=
    lt_of_lt_of_le H.baseAboveOne (H.criticalAboveBase _ δcrit)
  have δω : D.psi top < ω₁ := H.criticalCountable _ δcrit
  let δc := mkCountable (D.psi top) δω
  have key : ∀ e : CountableOrdinal, 1 ≤ e.val → e.val < D.psi top → (L e).val < D.psi top := by
    intro e h1 he
    have eq := levelBelow e h1 (he.trans hlt)
    have closed := (H.characterization top).2.1 (p e) (H.below e h1)
      (lt_of_le_of_lt (H.norm e h1) he)
    rwa [eq] at closed
  let oneC := mkCountable 1 (lt_trans δone δω)
  have keyAll : ∀ e : CountableOrdinal, e.val < D.psi top → (L e).val < D.psi top := by
    intro e he
    by_cases h1 : 1 ≤ e.val
    · exact key e h1 he
    · have small : e.val < oneC.val := not_le.1 h1
      exact (H.strict e oneC small).trans (key oneC le_rfl δone)
  rcases zero_or_succ_or_isSuccLimit (D.psi top) with h0 | ⟨c, hc⟩ | hl
  · exact absurd (lt_of_lt_of_eq δone h0) not_lt_zero
  · have hcl : c < D.psi top := by rw [← hc]; exact Order.lt_succ c
    let cc := mkCountable c (hcl.trans δω)
    have c1 : (1 : Ordinal.{0}) ≤ cc.val := by
      have one : (1 : Ordinal.{0}) < Order.succ c := by rw [hc]; exact δone
      exact Order.lt_succ_iff.1 one
    have Lc : (L cc).val ≤ cc.val := by
      have lt := keyAll cc hcl
      rw [← hc] at lt
      exact Order.lt_succ_iff.1 lt
    exact noFixedBelow cc c1 (hcl.trans hlt) (Subtype.ext (le_antisymm Lc (H.inflationary cc)))
  · have Lδ : (L δc).val ≤ δc.val := H.limit δc hl (D.psi top) (fun e he => (keyAll e he).le)
    exact noFixedBelow δc δone.le hlt (Subtype.ext (le_antisymm Lδ (H.inflationary δc)))

#print axioms exact_DiagonalCollapse

end LogicLineages.PersistentMarking.CollapseDiagonalProof
