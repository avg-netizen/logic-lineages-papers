module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions

@[expose] public section

/-! Paper 05, `foundations.tex`, `lem:saturation`, lines 199–208.

These are the full actual-ordinal source quantifiers below epsilon zero.
The norm and maximum are the independently defined actual-CNF norm and
actual finite-set maximum. No notation-domain implementation or new
transport proof is imported or assumed. The source's nonzero limit condition
is Mathlib's `Order.IsSuccLimit`. No optimized or encoded-effectiveness claim
is included.
-/

namespace LogicLineages.OrdinalComparison.Targets

def ActualLimitMaximumPredecessorSaturation : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a → ∀ b : Nat,
    actualOrdinalNorm (actualMaximumPredecessor a b) = b

def ActualLimitMaximumPredecessorStrictGrowth : Prop :=
  ∀ a : Ordinal.{0}, a < epsilonZero → Order.IsSuccLimit a →
    StrictMono (actualMaximumPredecessor a)

end LogicLineages.OrdinalComparison.Targets
