module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Cipher
open scoped BigOperators

/-- Four q-bit blocks leave room for both cross-product contributions. -/
def base (q : Nat) : Nat := 2^(4*q)

def sparseSum (n r : Nat) (e f : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.range n, f i*r^(e i)

/-- Only positions 2,4,8,... in base r may be occupied. The number of
positions is a genuinely varying natural parameter. -/
def encode (n q : Nat) (f : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.range n, f i * (base q)^(2^(i+1))

def shiftedEncode (n q : Nat) (f : Nat → Nat) : Nat :=
  ∑ i ∈ Finset.range n, f i * (base q)^(2^(i+2))

def ones (n q : Nat) : Nat := encode n q (fun _ => 1)
def shiftedOnes (n q : Nat) : Nat := shiftedEncode n q (fun _ => 1)

def Bounded (n q : Nat) (f : Nat → Nat) : Prop :=
  ∀ i, i < n → f i < 2^q

def IsCipherOf (n q : Nat) (f : Nat → Nat) (c : Nat) : Prop :=
  n+1 < q ∧ Bounded n q f ∧ c = encode n q f

/-- Explicit arithmetic characterization to be proved equivalent to the
actual two sparse all-ones sums. This is not their definition. -/
def OnesEquations (n q u u1 : Nat) : Prop :=
  n+1 < q ∧
    ((n=0 ∧ u=0 ∧ u1=0) ∨
      (0<n ∧ ∃ (w u2 : Nat),
        1+(base q-1)*w = base q * (base q)^(2^(n+1)) ∧
        u*u = u1+u2 ∧
        u1 = (u*u) &&& w ∧
        u2 = (u*u) &&& (2*w) ∧
        (base q)^2+u1 = u+(base q)^(2^(n+1)) ∧
        (base q)^4 ∣ u1))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Cipher
