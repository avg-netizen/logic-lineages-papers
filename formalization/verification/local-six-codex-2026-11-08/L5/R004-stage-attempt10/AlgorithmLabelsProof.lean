module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmTargets
public import LogicLineages.OrdinalComparison.FullWordGuardCompletion.ComparisonProof
public import Mathlib.Data.List.Count

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
open PolynomialGraphCompletion WordLinearDecisionCompletion Algorithm

def countBelow (xs : List Nat) (a : Nat) : Nat :=
  xs.countP (fun b => decide (b<a))

theorem countBelow_bound (xs : List Nat) (a : Nat) (ha : a ∈ xs) :
    countBelow xs a < xs.length := by
  apply List.countP_lt_length_iff.mpr
  exact ⟨a,ha,by simp⟩

theorem countBelow_mono (xs : List Nat) (a b : Nat) (hab : a ≤ b) :
    countBelow xs a ≤ countBelow xs b := by
  apply List.countP_mono_left
  intro x hx hxa
  have hxa' : x<a := by simpa using hxa
  have hxb : x<b := hxa'.trans_le hab
  simpa using hxb

theorem countBelow_strict (xs : List Nat) (a b : Nat) (ha : a ∈ xs) (hab : a<b) :
    countBelow xs a < countBelow xs b := by
  obtain ⟨before,after,hxs⟩ := List.append_of_mem ha
  subst xs
  have hlo := countBelow_mono before a b hab.le
  have hhi := countBelow_mono after a b hab.le
  simp only [countBelow] at hlo hhi ⊢
  simp [List.countP_append,List.countP_cons,hab]
  omega

theorem countBelow_order (xs : List Nat) (a b : Nat) (ha : a ∈ xs) (hb : b ∈ xs) :
    FullWordGuardCompletion.orderNat (countBelow xs a) (countBelow xs b) =
      FullWordGuardCompletion.orderNat a b := by
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h := countBelow_strict xs a b ha hab
    simp [FullWordGuardCompletion.orderNat,hab,h]
  · simp [FullWordGuardCompletion.orderNat]
  · have h := countBelow_strict xs b a hb hba
    simp [FullWordGuardCompletion.orderNat,not_lt_of_gt h,ne_of_gt h,
      not_lt_of_gt hba,ne_of_gt hba]

theorem assignments_membership (bound n : Nat) (labels : List Nat) :
    labels ∈ assignments bound n ↔
      labels.length = n ∧ ∀ a ∈ labels, a<bound := by
  induction n generalizing labels with
  | zero =>
      cases labels <;> simp [assignments]
  | succ n ih =>
      cases labels with
      | nil => simp [assignments]
      | cons a labels =>
          simp [assignments,ih,and_assoc,and_left_comm,and_comm]

private theorem zip_map_self {A B : Type} (xs : List A) (f : A → B) :
    xs.zip (xs.map f) = xs.map (fun a => (a,f a)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]

/-- These valuation-dependent values are used only to witness coverage of
the finite syntactic label enumeration. No runtime guard truth is queried. -/
noncomputable def actualValues (xs : List Item) (ν : Nat → Nat) : List Nat :=
  xs.map (fun a => wordValue (leader a).2 (ν a.2.1))

noncomputable def witnessLabels (xs : List Item) (ν : Nat → Nat) : List Nat :=
  (actualValues xs ν).map (countBelow (actualValues xs ν))

theorem witnessLabels_admitted (xs : List Item) (ν : Nat → Nat) :
    witnessLabels xs ν ∈ assignments xs.length xs.length := by
  apply (assignments_membership _ _ _).mpr
  constructor
  · simp [witnessLabels,actualValues]
  · intro label hl
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hl
    simpa [actualValues] using countBelow_bound (actualValues xs ν) a ha

theorem labelled_witness (r : Row) (ν : Nat → Nat) :
    labelled r (witnessLabels (active r) ν) =
      (active r).map (fun a =>
        (a,countBelow (actualValues (active r) ν) (wordValue (leader a).2 (ν a.2.1)))) := by
  unfold labelled witnessLabels actualValues
  simp only [List.map_map,Function.comp_def]
  exact zip_map_self _ _

theorem witness_pair_order (r : Row) (ν : Nat → Nat) (a b : Labelled)
    (ha : a ∈ labelled r (witnessLabels (active r) ν))
    (hb : b ∈ labelled r (witnessLabels (active r) ν)) :
    FullWordGuardCompletion.orderNat a.2 b.2 =
      FullWordGuardCompletion.orderNat
        (wordValue (leader a.1).2 (ν a.1.2.1))
        (wordValue (leader b.1).2 (ν b.1.2.1)) := by
  rw [labelled_witness] at ha hb
  obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hb
  apply countBelow_order
  · exact List.mem_map.mpr ⟨x,hx,rfl⟩
  · exact List.mem_map.mpr ⟨y,hy,rfl⟩

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmProof
