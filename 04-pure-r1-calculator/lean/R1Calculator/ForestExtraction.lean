import R1Calculator.ForestCapacity
import Mathlib.Data.Finset.Sort

/-!
# Extracting actual finite arithmetic interval forests

Every sorted finite configuration of the arithmetic candidate, with its
diagonal atoms, has an exact ordered-forest decomposition. The first row is
an initial block by interval closure. Transitivity forbids positive atoms
from that children block into the remaining forest. All negative cross-block
atoms and the original order of labels are retained in `Realizes`.

No semantic endpoint equivalence or universal forest-realization premise is
assumed. Arithmetic interval/transitivity laws and the separately proved
greedy realizations are actual theorems imported from their modules.
-/

noncomputable section

namespace R1Calculator.OrderedForest.Forest

open PureR1

private theorem prefix_cut : ∀ (n : Nat) (p : Fin n → Prop),
    (∀ i j, i ≤ j → p j → p i) →
    ∃ k : Nat, k ≤ n ∧ ∀ i, p i ↔ i.val < k := by
  intro n
  induction n with
  | zero =>
    intro p _
    exact ⟨0, le_rfl, fun i => Fin.elim0 i⟩
  | succ n ih =>
    intro p hp
    by_cases h0 : p 0
    · have htail : ∀ i j : Fin n, i ≤ j → p j.succ → p i.succ := by
        intro i j hij hj
        apply hp i.succ j.succ ?_ hj
        change i.val + 1 ≤ j.val + 1
        change i.val ≤ j.val at hij
        omega
      obtain ⟨k, hk, he⟩ := ih (fun i => p i.succ) htail
      refine ⟨k + 1, Nat.succ_le_succ hk, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact iff_of_true h0 (Nat.zero_lt_succ k)
      · simpa only [Fin.val_succ, Nat.add_lt_add_iff_right] using he j
    · refine ⟨0, Nat.zero_le _, ?_⟩
      intro i
      have hnot : ¬ p i := by
        intro hi
        apply h0
        apply hp 0 i ?_ hi
        change 0 ≤ i.val
        omega
      exact iff_of_false hnot (Nat.not_lt_zero _)

/-- Extract the full recursive induced forest on a sorted tuple. The size
equality identifies forest preorder vertices with the ORIGINAL tuple indices. -/
theorem extract_sorted : ∀ (n : Nat) (f : Fin n → Ordinal.{0}),
    StrictMono f → (∀ i, ArithmeticR1 (f i) (f i)) →
    ∃ F : Forest, ∃ e : F.size = n,
      Realizes F (fun i => f (Fin.cast e i)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro f hmono hdiag
    cases n with
    | zero => exact ⟨.nil, rfl, True.intro⟩
    | succ n =>
      let p : Fin n → Prop := fun i => ArithmeticR1 (f 0) (f i.succ)
      have hp : ∀ i j : Fin n, i ≤ j → p j → p i := by
        intro i j hij hj
        apply arithmeticR1_between hj
        · apply hmono.monotone
          change 0 ≤ i.val + 1
          omega
        · apply hmono.monotone
          change i.val + 1 ≤ j.val + 1
          change i.val ≤ j.val at hij
          omega
      obtain ⟨k, hk, hcut⟩ := prefix_cut n p hp
      obtain ⟨r, hkr⟩ : ∃ r : Nat, k + r = n := ⟨n - k, Nat.add_sub_of_le hk⟩
      let fc : Fin k → Ordinal.{0} :=
        fun i => f (Fin.cast hkr (Fin.castAdd r i)).succ
      let fr : Fin r → Ordinal.{0} :=
        fun i => f (Fin.cast hkr (Fin.natAdd k i)).succ
      have hfc : StrictMono fc := by
        intro i j hij
        apply hmono
        change i.val + 1 < j.val + 1
        change i.val < j.val at hij
        omega
      have hfr : StrictMono fr := by
        intro i j hij
        apply hmono
        change k + i.val + 1 < k + j.val + 1
        change i.val < j.val at hij
        omega
      have hkn : k < n + 1 := Nat.lt_succ_of_le hk
      have hrn : r < n + 1 := by omega
      obtain ⟨c, hc, hcR⟩ := ih k hkn fc hfc
        (fun i => hdiag (Fin.cast hkr (Fin.castAdd r i)).succ)
      obtain ⟨d, hd, hdR⟩ := ih r hrn fr hfr
        (fun i => hdiag (Fin.cast hkr (Fin.natAdd k i)).succ)
      subst k
      subst r
      subst n
      dsimp only [p] at hcut
      refine ⟨.cons c d, rfl, ?_⟩
      change Realizes (.cons c d) f
      refine ⟨hdiag 0, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [fc, Fin.cast_refl, id_eq] using hcR
      · simpa only [fr, Fin.cast_refl, id_eq] using hdR
      · intro i
        refine ⟨hmono ?_, ?_⟩
        · change 0 < i.val + 1
          omega
        · exact (hcut (Fin.castAdd d.size i)).mpr i.isLt
      · intro j
        refine ⟨hmono ?_, ?_⟩
        · change 0 < c.size + j.val + 1
          omega
        · intro h
          have hbad := (hcut (Fin.natAdd c.size j)).mp h
          change c.size + j.val < c.size at hbad
          omega
      · intro i j
        refine ⟨hmono ?_, ?_⟩
        · change i.val + 1 < c.size + j.val + 1
          have hi := i.isLt
          omega
        · intro hij
          have hrootc := (hcut (Fin.castAdd d.size i)).mpr i.isLt
          have hrootd := arithmeticR1_trans hrootc hij
          have hbad := (hcut (Fin.natAdd c.size j)).mp hrootd
          change c.size + j.val < c.size at hbad
          omega

/-- Every actual finite arithmetic-candidate configuration has a forest whose
preorder labels are its increasing enumeration, with no relabelling quotient. -/
theorem extract_finset (s : Finset Ordinal.{0})
    (hdiag : ∀ x ∈ s, ArithmeticR1 x x) :
    ∃ F : Forest, ∃ h : s.card = F.size, Realizes F (s.orderEmbOfFin h) := by
  classical
  let f : Fin s.card → Ordinal.{0} := s.orderEmbOfFin rfl
  obtain ⟨F, e, hf⟩ := extract_sorted s.card f (s.orderEmbOfFin rfl).strictMono
    (fun i => hdiag _ (s.orderEmbOfFin_mem rfl i))
  refine ⟨F, e.symm, ?_⟩
  have he : (fun i : Fin F.size => f (Fin.cast e i)) = s.orderEmbOfFin e.symm := by
    funext i
    exact (Finset.orderEmbOfFin_eq_orderEmbOfFin_iff
      (s := s) (h := rfl) (h' := e.symm) (i := Fin.cast e i) (j := i)).mpr rfl
  simpa only [he] using hf

/-- Semantic finite sets below a represented bound satisfy the diagonal
condition by actual notation coverage, rather than a notation-only premise. -/
theorem extract_finset_below (b : NONote) (s : Finset Ordinal.{0})
    (hs : ∀ x ∈ s, x ≤ b.repr) :
    ∃ F : Forest, ∃ h : s.card = F.size, Realizes F (s.orderEmbOfFin h) :=
  extract_finset s (fun x hx => arithmeticR1_refl_below b (hs x hx))

#print axioms extract_sorted
#print axioms extract_finset
#print axioms extract_finset_below

end R1Calculator.OrderedForest.Forest
