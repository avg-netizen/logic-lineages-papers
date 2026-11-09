module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainBranchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphTargets
open ExpandedGraph

def LiteralSubtraction : Prop := ∀ (z x y : Nat) (ν : Nat → Nat),
  ((subtraction z x y).eval ν ↔ ν z = ν x - ν y)
def LiteralDivision : Prop := ∀ (z x c : Nat) (ν : Nat → Nat),
  ((division z x c).eval ν ↔ ν z = ν x / c)
def LiteralInverse : Prop := ∀ (u z x : Nat) (ν : Nat → Nat),
  ((inverse u z x).eval ν ↔ ν u = ν z + 1 ∧ ν z = SnyatkovInverse.phiInverse (ν x))

def ExactAllocation : Prop := ∀ (start : Nat) (t : Term),
  0 < nodeCount t ∧ (allocated start t).Nodup ∧
    (∀ i, i ∈ allocated start t ↔ start ≤ i ∧ i < start + nodeCount t) ∧
    (Fresh start t → ∀ i ∈ allocated start t, i ∉ t.variables)
def ExactGraphSupport : Prop := ∀ (start : Nat) (t : Term),
  PlainBlockSplit.termHFree t = true → ∀ i : Nat,
    (i ∈ (graph start t).variables ↔ i ∈ t.variables ∨ i ∈ allocated start t)
def PlainOriginalGraphClass : Prop := ∀ (start : Nat) (t : Term),
  PlainBlockSplit.termHFree t = true → MaximalPlainBranch.isPlain (graph start t) = true

def GraphSoundness : Prop := ∀ (start : Nat) (t : Term) (ν : Nat → Nat),
  PlainBlockSplit.termHFree t = true →
    (graph start t).eval ν → ν (output start t) = t.value ν

def TotalGraphRealization : Prop := ∀ (start : Nat) (t : Term) (ν : Nat → Nat),
  PlainBlockSplit.termHFree t = true → Fresh start t → ∃ σ : Nat → Nat,
    (∀ i, i ∉ allocated start t → σ i = ν i) ∧
    (graph start t).eval σ ∧ σ (output start t) = t.value ν

def AllocatedNodeUniqueness : Prop := ∀ (start : Nat) (t : Term) (ν σ : Nat → Nat),
  PlainBlockSplit.termHFree t = true →
    (∀ i ∈ t.variables, ν i = σ i) →
    (graph start t).eval ν → (graph start t).eval σ →
    ∀ i ∈ allocated start t, ν i = σ i

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphTargets
