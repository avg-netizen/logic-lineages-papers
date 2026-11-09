module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmDefinitions
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open Algorithm

/-- The literal numeric sign payment absorbs all counter corrections,
retained raw-linear terms and the original integer constant. Q is the
largest strictly smaller leader, bounded by the actual Phi step gap. -/
theorem paid_sign_error (S A M B u P Q : Nat)
    (hpay : 64*(S+A+A*M+B+1) ≤ u) (hsquare : u*u < P)
    (hgap : 16*S*Q < P) :
    2*S*Q + 2*S*(u+1) + 2*A*(u+M) + 2*B < P := by
  let T := S+A+A*M+B+1
  let E := 2*S*(u+1)+2*A*(u+M)+2*B
  have hT : 1 ≤ T := by dsimp [T]; omega
  have hu : 64 ≤ u := by change 64*T ≤ u at hpay; omega
  have hE : E ≤ 2*T*(u+1) := by
    calc
      E ≤ E+(2*(A*M+B+1)*u+2*(A+1)) := Nat.le_add_right _ _
      _ = 2*T*(u+1) := by dsimp [E,T]; ring
  have hm : 64*T*(u+1) ≤ u*(u+1) := Nat.mul_le_mul_right (u+1) hpay
  have hE32 : 32*E ≤ u*(u+1) := by
    calc
      32*E ≤ 32*(2*T*(u+1)) := Nat.mul_le_mul_left 32 hE
      _ = 64*T*(u+1) := by ring
      _ ≤ u*(u+1) := hm
  have hE8 : 8*E < u*u := by nlinarith
  change 2*S*Q+E < P
  nlinarith

/-- An integer leading coefficient is separated from zero by one. Once the
entire concrete remainder is smaller than its actual positive leader, its
sign is the sign emitted by the runtime branch. -/
theorem dominant_integer_sign (L R : Int) (P error : Nat) (hL : L ≠ 0)
    (herror : error < P)
    (hlo : -(error : Int) ≤ R-L*(P : Int))
    (hhi : R-L*(P : Int) ≤ (error : Int)) :
    (L < 0 → R < 0) ∧ (¬L < 0 → 0 < R) := by
  have hcast : (error : Int) < (P : Int) := by exact_mod_cast herror
  have hP : (0 : Int) ≤ (P : Int) := by omega
  constructor
  · intro hn
    have hL' : L ≤ -1 := by omega
    have hmul := mul_le_mul_of_nonneg_right hL' hP
    linarith
  · intro hn
    have hL' : 1 ≤ L := by omega
    have hmul := mul_le_mul_of_nonneg_right hL' hP
    linarith

theorem sum_integer_intervals {α : Type} (xs : List α) (f : α → Int) (g : α → Nat)
    (h : ∀ a ∈ xs, -(g a : Int) ≤ f a ∧ f a ≤ (g a : Int)) :
    -(((xs.map g).sum : Nat) : Int) ≤ (xs.map f).sum ∧
      (xs.map f).sum ≤ (((xs.map g).sum : Nat) : Int) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have hs := ih (fun b hb => h b (by simp [hb]))
      simp only [List.map_cons,List.sum_cons,Nat.cast_add]
      constructor <;> linarith

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
