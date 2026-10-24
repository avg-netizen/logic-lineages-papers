import R1Calculator.ArithmeticBounds
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Ordered forests, normal weights and greedy ordinal placements

A forest is a list of rooted trees: `cons children rest` is its first root,
its children forest, and the remaining forest. Weights use ORDINAL addition
in the given order; they are not sorted or added commutatively. Thus a leaf
before a one-child tree has weight `1 + omega = omega`.

These are arithmetic constructions. Their induced realization and exact
minimum extent are proved in `ForestCapacity.lean`; neither property is
assumed as part of the syntax.
-/
namespace R1Calculator
namespace OrderedForest

inductive Forest where
  | nil
  | cons (children rest : Forest)
  deriving DecidableEq, Repr

namespace Forest

def size : Forest → Nat
  | .nil => 0
  | .cons c r => c.size + r.size + 1

def weight : Forest → ONote
  | .nil => 0
  | .cons c r => ONote.oadd c.weight 1 0 + r.weight

/-- Actual greedy extent, computed recursively, before identifying it with P(weight). -/
def width : Forest → ONote
  | .nil => 0
  | .cons c r => (ONote.oadd c.weight 1 0 + c.width) + r.width

def label : (F : Forest) → ONote → Fin F.size → ONote
  | .nil, _ => Fin.elim0
  | .cons c r, σ =>
      let root := σ + ONote.oadd c.weight 1 0
      Fin.cons root (Fin.append (c.label root) (r.label (root + c.width)))

/-- Endpoint after placing the complete forest; for the empty forest this
is the input cut, not the supremum of an empty set of labels. -/
def finish (F : Forest) (σ : ONote) : ONote := σ + F.width

@[simp] theorem weight_nil : Forest.nil.weight = 0 := rfl
@[simp] theorem width_nil : Forest.nil.width = 0 := rfl
@[simp] theorem size_nil : Forest.nil.size = 0 := rfl
@[simp] theorem size_cons (c r : Forest) : (Forest.cons c r).size = c.size + r.size + 1 := rfl

theorem weight_nf : ∀ F : Forest, ONote.NF F.weight
  | .nil => ONote.NF.zero
  | .cons c r => by
      haveI : ONote.NF c.weight := weight_nf c
      haveI : ONote.NF r.weight := weight_nf r
      exact ONote.add_nf _ _

theorem width_nf : ∀ F : Forest, ONote.NF F.width
  | .nil => ONote.NF.zero
  | .cons c r => by
      haveI : ONote.NF c.weight := weight_nf c
      haveI : ONote.NF c.width := width_nf c
      haveI : ONote.NF r.width := width_nf r
      exact ONote.add_nf _ _

theorem label_nf : ∀ (F : Forest) {σ : ONote}, ONote.NF σ →
    ∀ i, ONote.NF (F.label σ i)
  | .nil, _, _, i => Fin.elim0 i
  | .cons c r, σ, hσ, i => by
      haveI : ONote.NF σ := hσ
      haveI : ONote.NF c.weight := weight_nf c
      haveI : ONote.NF c.width := width_nf c
      have hroot : ONote.NF (σ + ONote.oadd c.weight 1 0) := ONote.add_nf _ _
      refine Fin.cases ?_ (fun j => ?_) i
      · exact hroot
      · refine Fin.addCases ?_ ?_ j
        · intro k
          simpa only [label, Fin.cons_succ, Fin.append_left] using label_nf c hroot k
        · intro k
          simpa only [label, Fin.cons_succ, Fin.append_right] using
            label_nf r (ONote.add_nf (σ + ONote.oadd c.weight 1 0) c.width) k

theorem weight_cons_repr (c r : Forest) :
    (Forest.cons c r).weight.repr = Ordinal.omega0 ^ c.weight.repr + r.weight.repr := by
  haveI : ONote.NF c.weight := weight_nf c
  haveI : ONote.NF r.weight := weight_nf r
  simp [weight, ONote.repr_add, ONote.repr]

theorem width_cons_repr (c r : Forest) :
    (Forest.cons c r).width.repr =
      (Ordinal.omega0 ^ c.weight.repr + c.width.repr) + r.width.repr := by
  haveI : ONote.NF c.weight := weight_nf c
  haveI : ONote.NF c.width := width_nf c
  haveI : ONote.NF r.width := width_nf r
  simp [width, ONote.repr_add, ONote.repr]

theorem finish_nf (F : Forest) {σ : ONote} (hσ : ONote.NF σ) : ONote.NF (F.finish σ) := by
  haveI : ONote.NF σ := hσ
  haveI : ONote.NF F.width := width_nf F
  exact ONote.add_nf _ _

theorem finish_repr (F : Forest) {σ : ONote} (hσ : ONote.NF σ) :
    (F.finish σ).repr = σ.repr + F.width.repr := by
  haveI : ONote.NF σ := hσ
  haveI : ONote.NF F.width := width_nf F
  exact ONote.repr_add _ _

@[simp] theorem label_cons_root (c r : Forest) (σ : ONote) :
    (Forest.cons c r).label σ (0 : Fin (c.size + r.size + 1)) = σ + ONote.oadd c.weight 1 0 := by
  simp only [label, Fin.cons_zero]

@[simp] theorem label_cons_child (c r : Forest) (σ : ONote) (i : Fin c.size) :
    (Forest.cons c r).label σ (Fin.castAdd r.size i).succ =
      c.label (σ + ONote.oadd c.weight 1 0) i := by
  simp only [label, Fin.cons_succ, Fin.append_left]

@[simp] theorem label_cons_rest (c r : Forest) (σ : ONote) (i : Fin r.size) :
    (Forest.cons c r).label σ (Fin.natAdd c.size i).succ =
      r.label ((σ + ONote.oadd c.weight 1 0) + c.width) i := by
  simp only [label, Fin.cons_succ, Fin.append_right]

/-- Every label is strictly after the cut and at or before its computed finish. -/
theorem label_bounds : ∀ (F : Forest) {σ : ONote}, ONote.NF σ → ∀ i,
    σ.repr < (F.label σ i).repr ∧ (F.label σ i).repr ≤ (F.finish σ).repr
  | .nil, _, _, i => Fin.elim0 i
  | .cons c r, σ, hσ, i => by
      haveI : ONote.NF σ := hσ
      haveI : ONote.NF c.weight := weight_nf c
      haveI : ONote.NF c.width := width_nf c
      haveI : ONote.NF r.width := width_nf r
      let root := σ + ONote.oadd c.weight 1 0
      let cut := root + c.width
      have hrnf : ONote.NF root := ONote.add_nf _ _
      have hcnf : ONote.NF cut := ONote.add_nf _ _
      have hroot : root.repr = σ.repr + Ordinal.omega0 ^ c.weight.repr := by
        simp only [root, ONote.repr_add, ONote.repr, PNat.one_coe,
          Nat.cast_one, mul_one, add_zero]
      have hcut : cut.repr = root.repr + c.width.repr := ONote.repr_add _ _
      have hrootlt : σ.repr < root.repr := by
        rw [hroot]
        exact lt_add_of_pos_right _ (Ordinal.opow_pos _ Ordinal.omega0_pos)
      have hfin : ((Forest.cons c r).finish σ).repr = cut.repr + r.width.repr := by
        rw [finish_repr _ hσ, width_cons_repr, hcut, hroot]
        simp only [add_assoc]
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [label_cons_root]
        refine ⟨hrootlt, ?_⟩
        rw [hfin]
        exact le_trans (show root.repr ≤ cut.repr by rw [hcut]; exact le_self_add)
          le_self_add
      · refine Fin.addCases ?_ ?_ j
        · intro k
          simp only [label_cons_child]
          obtain ⟨hl, hu⟩ := label_bounds c hrnf k
          refine ⟨lt_trans hrootlt hl, ?_⟩
          rw [hfin]
          exact le_trans hu le_self_add
        · intro k
          simp only [label_cons_rest]
          obtain ⟨hl, hu⟩ := label_bounds r hcnf k
          refine ⟨lt_of_lt_of_le hrootlt ?_, ?_⟩
          · exact le_trans (show root.repr ≤ cut.repr by rw [hcut]; exact le_self_add) hl.le
          · simpa only [finish_repr r hcnf, hfin] using hu

#print axioms label_bounds

#print axioms weight_nf
#print axioms label_nf
end Forest
end OrderedForest
end R1Calculator
