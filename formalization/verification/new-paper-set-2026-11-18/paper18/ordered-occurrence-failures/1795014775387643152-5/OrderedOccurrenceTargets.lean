module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceTargets
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence
open NormalForm (Formula Summand)

def ExactRoster : Prop := ∀ p r j c s,
  (r,j,c,s) ∈ roster p ↔ ∃ row, (rows p)[r]?=some row ∧ row.2[j]?=some (c,s)
def ExactLive : Prop := ∀ xs p o,
  o ∈ live xs p ↔ o ∈ roster p ∧ coefficient o ≠ 0 ∧ nonlinear (summand o)=true ∧ (summand o).name ∈ xs
def ExactInactive : Prop := ∀ xs p i,
  i ∈ inactive xs p ↔ i ∈ xs ∧ ∀ o ∈ live xs p, (summand o).name ≠ i

def OrderedCoverage : Prop := ∀ xs, xs.Nodup → ∀ ν : Nat → Nat,
  (∃ i ∈ xs, ∃ j ∈ xs, i ≠ j ∧ ν i=ν j) ∨
    ∃ ys ∈ xs.permutations, (strictOrder ys).eval ν

def MaximumCoverage : Prop := ∀ xs p, live xs p ≠ [] → ∀ ν : Nat → Nat,
  ∃ o ∈ live xs p, (maximal xs p o).eval ν

def TieReduction : Prop := ∀ xs p i j, xs.Nodup → i ∈ xs → j ∈ xs → i ≠ j →
  (∀ ν, HyperCloseBlock.existsNames xs (.conjunction (.equal (.variable i) (.variable j)) p.compile) ν ↔
    HyperCloseBlock.existsNames (xs.erase i) (p.compile.substitute i (.variable j)) ν) ∧
  (xs.erase i).Nodup ∧ (xs.erase i).length+1=xs.length ∧ (xs.erase i).length<xs.length

def FullCoverage : Prop := ∀ xs p, xs.Nodup → ∀ ν,
  HyperCloseBlock.existsNames xs p.compile ν ↔ ∃ o ∈ dispatch xs p, holds o ν

def ContinuationProvenance : Prop := ∀ xs p o, xs.Nodup → o ∈ dispatch xs p →
  (o.tag=0 → xs=[] ∧ o.bound=[] ∧ o.matrix=p.compile) ∧
  (o.tag=1 → o.bound=xs ∧ o.witness ∈ inactive xs p ∧ o.matrix=p.compile) ∧
  (o.tag=2 → o.bound.length+1=xs.length ∧ o.bound.length<xs.length) ∧
  (o.tag=3 → o.bound.Perm xs ∧ ∃ a,
    (live xs p)[o.occurrence]?=some a ∧ o.witness=(summand a).name ∧
    o.matrix=.conjunction (strictOrder o.bound) (.conjunction (maximal xs p a) p.compile)) ∧
  (o.tag=0 ∨ o.tag=1 ∨ o.tag=2 ∨ o.tag=3)
def FreeSupport : Prop := ∀ xs p o, xs.Nodup → o ∈ dispatch xs p →
  ∀ name, name ∈ o.matrix.variables → name ∉ o.bound → name ∈ p.variables ∧ name ∉ xs

def Programs : Prop := ∃ program : (List Nat × Nat) → List (Nat × List Nat × Nat × Nat × Nat),
  Computable program ∧ ∀ xs p, program (xs,p.encode)=(dispatch xs p).map outputCode

def Full : Prop := ExactRoster ∧ ExactLive ∧ ExactInactive ∧ OrderedCoverage ∧
  MaximumCoverage ∧ TieReduction ∧ FullCoverage ∧ ContinuationProvenance ∧ FreeSupport ∧ Programs
end LogicLineages.StandardControlCurrent.OrderedOccurrenceTargets
