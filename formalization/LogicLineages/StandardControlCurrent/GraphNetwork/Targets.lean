module
public import LogicLineages.StandardControlCurrent.GraphNetwork.Definitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.GraphNetwork.Targets
open OrdinalComparison PolynomialGraphCompletion WordLinearDecisionCompletion

def LiteralNetwork : Prop :=
  (∀ b : Block, Code.blockRows (encodeBlock b) = b.rows) ∧
  (∀ d hs bs rs p, Code.package d (sourceCode hs bs rs p) =
    (degree hs bs, Formula.encode (matrix d hs bs rs p)))

def Programs : Prop :=
  Computable (fun a : Nat × Nat => Code.package a.1 a.2) ∧
  Computable (fun a : Nat × Nat => Code.decide a.1 a.2) ∧
  Computable (fun a : Nat × List (Nat × Nat) => Code.allocate a.1 a.2)

def FreshCoverage : Prop :=
  (∀ n xs, InputBound n xs → AllocationGood n (allocate n xs)) ∧
  (∀ start xs, (allocate start xs).map (fun b => (b.term,b.result)) = xs) ∧
  (∀ start xs, Code.allocate start (xs.map (fun x => (x.1.encode,x.2))) =
    (allocate start xs).map encodeBlock)

/-- Genuine single-block graph semantics with exact result linkage and frame.
Global fresh allocation above makes these blocks valid simultaneous graph
translations; the decision core itself also permits literal collisions. -/
def BlockCoverage : Prop := ∀ (b : Block), ValidExpr b.term →
  Fresh b.start b.term → b.result < b.start → ∀ ν : Nat → Nat,
  (∃ σ : Nat → Nat, (∀ i, i ∉ allocated b.start b.term → σ i = ν i) ∧
    RowsHold b.rows σ) ↔ ν b.result = b.term.value ν

def DomainsAndSemantics : Prop := ∀ d hs bs rs p, Valid hs bs rs p →
  3 ≤ degree hs bs ∧ Formula.allowed (degree hs bs) (matrix d hs bs rs p) ∧
  (∀ ν : Nat → Nat, Formula.meaningful (matrix d hs bs rs p) ν) ∧
  (∀ ν : Nat → Nat, Formula.eval ν (matrix d hs bs rs p) ↔ SourceHolds d hs bs rs p ν)

/-- Arbitrary finite canonical graph networks, including cycles/shared names;
only original inputs are positive, every other graph wire remains natural. -/
def NetworkDecision : Prop := ∀ d hs bs rs p, Valid hs bs rs p →
  (Code.decide d (sourceCode hs bs rs p) = true ↔ ∃ ν : Nat → Nat, SourceHolds d hs bs rs p ν)

def FullGraphDomains : Prop := LiteralNetwork ∧ Programs ∧ FreshCoverage ∧ BlockCoverage ∧
  DomainsAndSemantics ∧ NetworkDecision

end LogicLineages.StandardControlCurrent.GraphNetwork.Targets
