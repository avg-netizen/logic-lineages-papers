module
public import LogicLineages.OrdinalComparison.Definitions
public import LogicLineages.OrdinalComparison.ControlTargets

@[expose] public section

/-!
# Independent source-level component targets

This file contains no proofs and imports no new proof implementations.
It records exact components of paper05's finite-ball and numerical-control
lemmas. It does not declare those whole lemmas complete: the finite-ball
lemma additionally contains natural arithmetic algorithms/additivity, and
the control lemma additionally asserts a computability property.

The proposition definitions are statement signatures to be inhabited by
separate proofs. No axiom or theorem supplies an inhabitant here.
-/

namespace LogicLineages.OrdinalComparison.Targets

/-- Finiteness portion of foundations `lem:finite-balls`, on normal CNF inputs. -/
def FiniteNormalNormBalls : Prop :=
  ∀ b : Nat, Set.Finite {a : NONote | Vendor.R1.treeWeight a.1 ≤ b}

/-- An exact enumerator interface, without an asserted machine-code bridge. -/
def ExactNormalNormEnumerator (enumerate : Nat → Finset NONote) : Prop :=
  ∀ (b : Nat) (a : NONote),
    a ∈ enumerate b ↔ Vendor.R1.treeWeight a.1 ≤ b

end LogicLineages.OrdinalComparison.Targets
