module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchTargets
open NormalForm MaximalPlainBranch

def LiteralFrame : Prop := ∀ (i : Nat) (p : Formula) (ν : Nat → Nat),
  (frame i p).eval ν ↔ cutoff p ≤ ν i ∧ ∀ j ∈ p.variables, ν j ≤ ν i

def LiteralFrameLinearity : Prop := ∀ (i : Nat) (p : Formula),
  LinearRows.isLinear i (frame i p) = true

def ActualContextualCompilation : Prop := ∀ (i : Nat) (p : Formula), isPlain p = true →
  ∀ ν : Nat → Nat, cutoff p ≤ ν i → (∀ j ∈ p.variables, ν j ≤ ν i) →
    ((compile i p).eval ν ↔ p.eval ν)

def LiteralContextualLinearity : Prop := ∀ (i : Nat) (p : Formula), isPlain p = true →
  LinearRows.isLinear i (framed i p) = true

/-- The quantifier covers exactly the materialized large/maximal-name branch.
This is not a claim that this branch exhausts all witnesses. -/
def ActualExistentialBranch : Prop := ∀ (i : Nat) (p : Formula), isPlain p = true →
  ∀ ν : Nat → Nat, (eliminate i p).eval ν ↔
    ∃ n : Nat, cutoff p ≤ n ∧
      (∀ j ∈ p.variables, (Function.update ν i n) j ≤ n) ∧
      p.eval (Function.update ν i n)

def ExactRemovedName : Prop := ∀ (i : Nat) (p : Formula),
  i ∉ (eliminate i p).variables

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchTargets
