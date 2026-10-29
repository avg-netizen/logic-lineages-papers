module
public import LogicLineages.OrdinalComparison.Definitions

@[expose] public section

/-!
# Independent specification of the norm-controlled collapse

The source collapse is the least natural upper bound of all values `c b + 1`
at strict ordinal predecessors satisfying the original norm budget. Natural
numbers are already bounded below by zero, so this includes the source's
extra `{0}` in its finite maximum. No predecessor enumerator or implementation
is imported here.
-/

namespace LogicLineages.OrdinalComparison.Targets

def NormControlledCollapse (c : NONote → Nat) : Prop :=
  ∀ a : NONote,
    (∀ b : NONote, b < a →
      Vendor.R1.treeWeight b.1 ≤ Phi (Vendor.R1.treeWeight a.1) →
      c b + 1 ≤ c a) ∧
    (∀ k : Nat,
      (∀ b : NONote, b < a →
        Vendor.R1.treeWeight b.1 ≤ Phi (Vendor.R1.treeWeight a.1) →
        c b + 1 ≤ k) → c a ≤ k)

def UniqueNormControlledCollapse : Prop :=
  ∃ c : NONote → Nat, NormControlledCollapse c ∧
    ∀ d : NONote → Nat, NormControlledCollapse d → d = c

def FiniteCollapseValues (c : NONote → Nat) : Prop :=
  ∀ n : Nat, c (NONote.ofNat n) = n

def CollapseDominatesNorm (c : NONote → Nat) : Prop :=
  ∀ a : NONote, Vendor.R1.treeWeight a.1 ≤ c a

end LogicLineages.OrdinalComparison.Targets
