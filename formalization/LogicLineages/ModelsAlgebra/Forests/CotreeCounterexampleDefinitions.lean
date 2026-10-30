module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.List.Chain
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Card

/-! Literal finite cotrees and the path interpretation in Carter v1's
introduction. Root self-parent is never a tree edge. No cotree transfer theorem
or correctness of raw data is assumed. The counterexample concerns only this
interpretation, not the final decidability theorem. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.CotreeCounterexample

inductive Label where
  | leaf | union | join
  deriving DecidableEq

structure CotreeData (n : Nat) where
  root : Fin n
  parent : Fin n → Fin n
  label : Fin n → Label

def child {n} (T : CotreeData n) (x y : Fin n) : Prop :=
  y ≠ T.root ∧ T.parent y = x

instance {n} (T : CotreeData n) : DecidableRel (child T) :=
  fun x y => inferInstanceAs (Decidable (y ≠ T.root ∧ T.parent y = x))

def ancestor {n} (T : CotreeData n) (x y : Fin n) : Prop :=
  ∃ d : Fin (n + 1), (T.parent^[d.val]) y = x

instance {n} (T : CotreeData n) : DecidableRel (ancestor T) :=
  fun x y => inferInstanceAs (Decidable (∃ d : Fin (n + 1), (T.parent^[d.val]) y = x))

def ValidCotree {n} (T : CotreeData n) : Prop :=
  T.parent T.root = T.root ∧
  (∀ x, ancestor T T.root x) ∧
  (∀ x, T.label x = .leaf ↔ ∀ y, ¬ child T x y) ∧
  (∀ x, T.label x ≠ .leaf → 2 ≤ (Finset.univ.filter (child T x)).card) ∧
  (∀ x y, child T x y → T.label x ≠ .leaf → T.label y ≠ .leaf → T.label x ≠ T.label y)

def IsLCA {n} (T : CotreeData n) (x y z : Fin n) : Prop :=
  ancestor T z x ∧ ancestor T z y ∧
    ∀ w, ancestor T w x → ancestor T w y → ancestor T w z

def joinLCA {n} (T : CotreeData n) (x y : Fin n) : Prop :=
  ∃ z, IsLCA T x y z ∧ T.label z = .join

def evaluatedGraph {n m} (T : CotreeData n) (leaves : Fin m → Fin n) : SimpleGraph (Fin m) :=
  SimpleGraph.fromRel (fun i j => joinLCA T (leaves i) (leaves j))

abbrev Edge {n} (T : CotreeData n) := { e : Fin n × Fin n // child T e.1 e.2 }

def pathEdges {n} (p : List (Fin n)) : Finset (Fin n × Fin n) :=
  (p.zip p.tail).toFinset

/-- Exact downward, pairwise-edge-disjoint paths, with original labels but
no extra ancestor-reflection requirement. The root image is unrestricted. This is not an ordinary
order-forest embedding and is not substituted for one anywhere. -/
structure PathCotreeEmbedding {n m} (S : CotreeData n) (T : CotreeData m) where
  nodeMap : Fin n ↪ Fin m
  labels : ∀ x, T.label (nodeMap x) = S.label x
  path : Edge S → List (Fin m)
  path_start : ∀ e, (path e).head? = some (nodeMap e.val.1)
  path_end : ∀ e, (path e).getLast? = some (nodeMap e.val.2)
  path_downward : ∀ e, (path e).IsChain (child T)
  edge_disjoint : ∀ e d, e ≠ d → Disjoint (pathEdges (path e)) (pathEdges (path d))

def sourceCotree : CotreeData 4 where
  root := 0
  parent := fun _ => 0
  label := fun x => if x = 0 then .union else .leaf

def hostCotree : CotreeData 7 where
  root := 0
  parent := fun x => if x.val ≤ 2 then 0 else if x.val ≤ 4 then 2 else 4
  label := fun x => if x = 0 ∨ x = 4 then .union else if x = 2 then .join else .leaf

def sourceLeaves (i : Fin 3) : Fin 4 := i.succ

def hostLeaves : Fin 4 → Fin 7 := ![1, 3, 5, 6]

/-- Vertex 0 isolated; vertex 1 is the center of the path with endpoints 2,3. -/
def isolatedPathGraph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel (fun i j => i = 1 ∧ (j = 2 ∨ j = 3))

end LogicLineages.ModelsAlgebra.Forests.CotreeCounterexample
