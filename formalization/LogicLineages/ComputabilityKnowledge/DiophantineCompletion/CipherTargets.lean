module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherTargets
open Dioph Cipher
open scoped BigOperators

def SparseNumberBound : Prop := ∀ (n r top : Nat) (e f : Nat → Nat),
  2≤r → (∀ i j, i<j → j<n → e i<e j) →
  (∀ i, i<n → f i<r) → (∀ i, i<n → e i<top) →
  sparseSum n r e f < r^top

def SparseDigitExtraction : Prop := ∀ (n r : Nat) (e f : Nat → Nat),
  2≤r → (∀ i j, i<j → j<n → e i<e j) →
  (∀ i, i<n → f i<r) →
  ∀ i, i<n → (sparseSum n r e f / r^(e i)) % r = f i

def SparseAllDigitExtraction : Prop := ∀ (n r : Nat) (e f : Nat → Nat),
  2≤r → (∀ i j, i<j → j<n → e i<e j) →
  (∀ i, i<n → f i<r) →
  ∀ k, (sparseSum n r e f / r^k) % r =
    ∑ i ∈ Finset.range n, if e i=k then f i else 0

def CipherDigitExtraction : Prop := ∀ (n q : Nat) (f : Nat → Nat),
  n+1 < q → Bounded n q f →
  ∀ i, i<n → (encode n q f / (base q)^(2^(i+1))) % base q = f i

def CipherInjectivity : Prop := ∀ (n q : Nat) (f g : Nat → Nat),
  n+1 < q → Bounded n q f → Bounded n q g →
  (encode n q f = encode n q g ↔ ∀ i, i<n → f i=g i)

def CipherAddition : Prop := ∀ (n q : Nat) (a b c : Nat → Nat),
  n+1 < q → Bounded n q a → Bounded n q b → Bounded n q c →
  (encode n q a = encode n q b + encode n q c ↔ ∀ i, i<n → a i=b i+c i)

def CipherProductMask : Prop := ∀ (n q : Nat) (b c : Nat → Nat),
  n+1 < q → Bounded n q b → Bounded n q c →
  (encode n q b * encode n q c) &&& ((base q-1)*shiftedOnes n q) =
    shiftedEncode n q (fun i => b i*c i)

def CipherMultiplication : Prop := ∀ (n q : Nat) (a b c : Nat → Nat),
  n+1 < q → Bounded n q a → Bounded n q b → Bounded n q c →
  ((encode n q a * ones n q) &&& ((base q-1)*shiftedOnes n q) =
    (encode n q b * encode n q c) &&& ((base q-1)*shiftedOnes n q) ↔
      ∀ i, i<n → a i=b i*c i)

def OnesArithmeticCharacterization : Prop := ∀ (n q u u1 : Nat),
  (n+1<q ∧ u=ones n q ∧ u1=shiftedOnes n q) ↔ OnesEquations n q u u1

def CipherValidityCharacterization : Prop := ∀ (n q a : Nat),
  (∃ f : Nat → Nat, IsCipherOf n q f a) ↔
    n+1<q ∧ a &&& ((2^q-1)*ones n q) = a

/-- Full variable-input sparse-ones relation. A premise asserting that this
relation is Diophantine must never replace its actual proof. -/
def OnesDiophantine : Prop :=
  Dioph {v : Fin 4 → Nat |
    v 0+1<v 1 ∧ v 2=ones (v 0) (v 1) ∧ v 3=shiftedOnes (v 0) (v 1)}

/-- The complete variable-bound closure needed by original-code recursion
and minimization. Fixed finite conjunction is not this target. -/
def VariableBoundedUniversalClosure : Prop :=
  ∀ (n : Nat) (bound : (Fin n → Nat) → Nat) (R : Nat → (Fin n → Nat) → Prop),
    DiophFn bound →
    Dioph {w : Option (Fin n) → Nat | R (w none) (w ∘ some)} →
    Dioph {v : Fin n → Nat | ∀ i, i<bound v → R i v}

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherTargets
