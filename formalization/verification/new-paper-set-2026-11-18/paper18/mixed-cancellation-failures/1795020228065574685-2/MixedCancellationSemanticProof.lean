module
public import LogicLineages.StandardControlCurrent.MixedCancellationPartitionProof
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceRosterProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormSemanticProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedCancellation
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

private theorem weighted_constant (xs : List (Int × Summand)) (ν : Nat → Nat) (v : Nat)
    (h : ∀ a ∈ xs, a.2.term.value ν = v) :
    (xs.map (fun a => a.1*(a.2.term.value ν : Int))).sum =
      (xs.map Prod.fst).sum * (v : Int) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have ht : ∀ b ∈ xs, b.2.term.value ν = v := fun b hb => h b (by simp [hb])
      simp only [List.map_cons,List.sum_cons,ha,ih ht]
      ring

theorem cancellation : MixedCancellationTargets.Cancellation := by
  intro r bs hl hz ν hg
  have hp := partition r bs hl ν
  have hs : ((selected r bs).map (fun a => a.1*(a.2.term.value ν : Int))).sum = 0 := by
    cases he : selected r bs with
    | nil => simp [he]
    | cons a as =>
        have hg' : ∀ b ∈ as, b.2.term.value ν = a.2.term.value ν := by
          intro b hb
          have hh := (OrderedOccurrenceProof.all_eval _ ν).mp
            (show (OrderedOccurrence.all (as.map fun b => Matrix.equal b.2.term a.2.term)).eval ν from
              by simpa only [equalGuard,he] using hg)
          exact hh (.equal b.2.term a.2.term) (List.mem_map.mpr ⟨b,hb,rfl⟩)
        have hc : ∀ b ∈ a::as, b.2.term.value ν = a.2.term.value ν := by
          intro b hb
          rcases List.mem_cons.mp hb with h | h
          · subst b; rfl
          · exact hg' b h
        have hw := weighted_constant (a::as) ν (a.2.term.value ν) hc
        have hz' : ((a::as).map Prod.fst).sum = 0 := by
          simpa only [coefficientSum,he] using hz
        rw [he,hw,hz',zero_mul]
  omega

theorem context_eval (c : Context) (p q : Matrix) (ν : Nat → Nat)
    (h : p.eval ν ↔ q.eval ν) : (c.plug p).eval ν ↔ (c.plug q).eval ν := by
  induction c with
  | hole => exact h
  | neg c ih => exact not_congr ih
  | conjLeft c r ih => exact and_congr ih Iff.rfl
  | conjRight r c ih => exact and_congr Iff.rfl ih
  | disjLeft c r ih => exact or_congr ih Iff.rfl
  | disjRight r c ih => exact or_congr Iff.rfl ih

theorem guardedSemantics : MixedCancellationTargets.GuardedSemantics := by
  intro c a bs ν
  by_cases hen : enabled a.row bs = true
  · have hh : bs.length = a.row.2.length ∧ coefficientSum a.row bs = 0 := by
      have he := hen
      simp only [enabled,Bool.and_eq_true,beq_iff_eq] at he
      exact ⟨he.1.1,he.1.2⟩
    simp only [step,hen,if_true,rewritten,before,Matrix.eval]
    apply and_congr_right
    intro hg
    have hv := cancellation a.row bs hh.1 hh.2 ν hg
    apply context_eval
    change (domainFormula a.row).compile.eval ν ∧ (replaceRow a (retained a.row bs)).compile.eval ν ↔
      (domainFormula a.row).compile.eval ν ∧ a.compile.eval ν
    apply and_congr Iff.rfl
    rw [NormalFormSemanticProof.actualAtomCompilation,NormalFormSemanticProof.actualAtomCompilation]
    cases a <;> simp only [replaceRow,Atom.eval,Atom.row] at * <;> rw [hv]
  · simp [step,hen]
end LogicLineages.StandardControlCurrent.MixedCancellation
