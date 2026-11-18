module
public import LogicLineages.CartierObserverCurrent.SplittingRootsDefinitions

@[expose] public section
namespace LogicLineages.CartierObserverCurrent.SplittingRoots.Targets

def FiniteFieldAndRoots : Prop := ∀ d : Nat, Finite (FieldAt d) ∧ Finite (Root d)

def ActualSplitting : Prop := ∀ d : Nat, (splitPolynomial d).Splits

def ExactAllRoots : Prop :=
  ∀ d : Nat, ∀ z : FieldAt d, z ∈ rootSet d ↔ (splitPolynomial d).eval z = 0

def NonzeroRoots : Prop := ∀ d : Nat, ∀ z : Root d, z.val ≠ 0

def FrobeniusFixedPolynomial : Prop :=
  ∀ d : Nat, (splitPolynomial d).map (frobenius (FieldAt d) 2) = splitPolynomial d

def FrobeniusRootPermutation : Prop :=
  ∀ d : Nat, ∃ e : Equiv.Perm (Root d), ∀ z : Root d, (e z).val = z.val ^ 2

def FixedFieldExactlyF2 : Prop :=
  ∀ d : Nat, ∀ x : FieldAt d, x ^ 2 = x ↔
    ∃! a : ZMod 2, algebraMap (ZMod 2) (FieldAt d) a = x
end LogicLineages.CartierObserverCurrent.SplittingRoots.Targets
