module

public import LogicLineages.ModelsAlgebra.Forests.HostReductionDefinitions
public import Mathlib.Computability.Primrec.List
public import Mathlib.Data.List.Sublists

/-! Explicit finite input data and bounded exhaustive tests for paper 03.
No arbitrary mathematical forest bundle is presumed effectively encoded.
The mathematical decoder's proofs merely build the checked partial-order
structure. Search over unbounded pairs and Carter's algorithm are not defined. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.FiniteCode

abbrev Code := ℕ × List (ℕ × ℕ)

def encode (c : Code) : ℕ := Encodable.encode c
def decode (n : ℕ) : Option Code := Encodable.decode n

def Rel (c : Code) (i j : ℕ) : Prop := (i, j) ∈ c.2

instance relDecidable (c : Code) : DecidableRel (Rel c) := fun _ _ => inferInstanceAs (Decidable (_ ∈ c.2))

def ForestPredicate (c : Code) : Prop :=
  (∀ e ∈ c.2, e.1 < c.1 ∧ e.2 < c.1) ∧
  (∀ i ∈ List.range c.1, Rel c i i) ∧
  (∀ i ∈ List.range c.1, ∀ j ∈ List.range c.1, Rel c i j → Rel c j i → i = j) ∧
  (∀ i ∈ List.range c.1, ∀ j ∈ List.range c.1, ∀ k ∈ List.range c.1,
    Rel c i j → Rel c j k → Rel c i k) ∧
  (∀ i ∈ List.range c.1, ∀ j ∈ List.range c.1, ∀ k ∈ List.range c.1,
    Rel c i k → Rel c j k → Rel c i j ∨ Rel c j i)

instance forestPredicateDecidable (c : Code) : Decidable (ForestPredicate c) := by
  unfold ForestPredicate
  infer_instance

def valid (c : Code) : Bool := decide (ForestPredicate c)

/-- The actual finite order forest induced by a validated relation matrix. -/
def toForest (c : Code) (hc : valid c = true) : FiniteOrderForest := by
  have hv : ForestPredicate c := of_decide_eq_true hc
  let po : PartialOrder (Fin c.1) := {
    le := fun i j => Rel c i.val j.val
    lt := fun i j => Rel c i.val j.val ∧ ¬ Rel c j.val i.val
    lt_iff_le_not_ge := fun _ _ => Iff.rfl
    le_refl := fun i => hv.2.1 i.val (List.mem_range.mpr i.isLt)
    le_antisymm := fun i j hij hji => Fin.ext
      (hv.2.2.1 i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt) hij hji)
    le_trans := fun i j k hij hjk => hv.2.2.2.1
      i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      k.val (List.mem_range.mpr k.isLt) hij hjk }
  exact {
    Carrier := Fin c.1
    carrierFintype := inferInstance
    carrierPartialOrder := po
    forest := fun {i j k} hik hjk => hv.2.2.2.2
      i.val (List.mem_range.mpr i.isLt) j.val (List.mem_range.mpr j.isLt)
      k.val (List.mem_range.mpr k.isLt) hik hjk }

def allPairs (n : ℕ) : List (ℕ × ℕ) :=
  (List.range n).flatMap fun i => (List.range n).map fun j => (i, j)

def allRelations (n : ℕ) : List Code :=
  (allPairs n).sublists.map fun edges => (n, edges)

def hostCodes (N : ℕ) : List Code :=
  (List.range (N + 1)).flatMap allRelations

/-- Every length-n list over vertices below m, including the unique empty
map when n=0 and no maps from a nonempty domain into m=0. -/
def mapWords : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, m => (List.range m).flatMap fun a => (mapWords n m).map (List.cons a)

def MapPredicate (c d : Code) (xs : List ℕ) : Prop :=
  xs.length = c.1 ∧ (∀ a ∈ xs, a < d.1) ∧
  (∀ i ∈ List.range c.1, ∀ j ∈ List.range c.1,
    xs.getD i 0 = xs.getD j 0 → i = j) ∧
  (∀ i ∈ List.range c.1, ∀ j ∈ List.range c.1,
    Rel d (xs.getD i 0) (xs.getD j 0) ↔ Rel c i j)

instance mapPredicateDecidable (c d : Code) (xs : List ℕ) : Decidable (MapPredicate c d xs) := by
  unfold MapPredicate
  infer_instance

def mapTest (c d : Code) (xs : List ℕ) : Bool := decide (MapPredicate c d xs)

def EmbeddingPredicate (c d : Code) : Prop :=
  ∃ xs ∈ mapWords c.1 d.1, MapPredicate c d xs

instance embeddingPredicateDecidable (c d : Code) : Decidable (EmbeddingPredicate c d) := by
  unfold EmbeddingPredicate
  infer_instance

def embeddingTest (c d : Code) : Bool := decide (EmbeddingPredicate c d)

def FamilyValid (U : List Code) : Prop := ∀ c ∈ U, valid c = true

def toFamily (U : List Code) (hU : FamilyValid U) : List FiniteOrderForest :=
  U.attach.map fun c => toForest c.val (hU c.val c.property)

def PermittedPredicate (U : List Code) (c : Code) : Prop :=
  ForestPredicate c ∧ ∀ B ∈ U, ForestPredicate B ∧ ¬ EmbeddingPredicate B c

instance permittedPredicateDecidable (U : List Code) (c : Code) :
    Decidable (PermittedPredicate U c) := by
  unfold PermittedPredicate
  infer_instance

def permittedTest (U : List Code) (c : Code) : Bool := decide (PermittedPredicate U c)

def BoundedHostPredicate (U : List Code) (c d : Code) : Prop :=
  ∃ H ∈ hostCodes (c.1 + d.1),
    PermittedPredicate U H ∧ EmbeddingPredicate c H ∧ EmbeddingPredicate d H

instance boundedHostPredicateDecidable (U : List Code) (c d : Code) :
    Decidable (BoundedHostPredicate U c d) := by
  unfold BoundedHostPredicate
  infer_instance

def boundedHostTest (U : List Code) (c d : Code) : Bool := decide (BoundedHostPredicate U c d)

def negativePairTest (U : List Code) (c d : Code) : Bool :=
  permittedTest U c && permittedTest U d && !(boundedHostTest U c d)

end LogicLineages.ModelsAlgebra.Forests.FiniteCode
