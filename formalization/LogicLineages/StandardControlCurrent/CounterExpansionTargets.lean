module
public import LogicLineages.StandardControlCurrent.CounterExpansionDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.CounterExpansionTargets
open OrdinalComparison NumericalKernel CounterExpansion

/-- Every actual dynamic input pays its own shifted mass; all ladder identities
are conclusions, never an oracle supplied by the caller. -/
def LadderCalibration : Prop := ∀ n c t : Nat, c+2*(n+3)+1 ≤ t →
  (∀ p ∈ entries n c t, t ≤ p.2 ∧ 3 ≤ p.1 ∧ p.1 ≤ n+3 ∧ c+2*p.1+1 ≤ p.2) ∧
  entries n c t = CounterLeaderExpansion.entries n c t ∧
  bottomInput n c t = CounterLeaderExpansion.bottomInput n c t ∧
  leaderPreimage n c t = CounterLeaderExpansion.leaderPreimage n c t ∧
  leader n c t = CounterLeaderExpansion.leader n c t ∧
  residuals n c t = CounterLeaderExpansion.residuals n c t

def UpperCalibration : Prop := ∀ k m c t : Nat, c+2*(m+k+3)+1 ≤ t →
  (∀ p ∈ upperEntries k m c t, t ≤ p.2 ∧ m+3 < p.1 ∧ p.1 ≤ m+k+3 ∧ c+2*p.1+1 ≤ p.2) ∧
  alignedInput k m c t = CounterLeaderCollision.alignedInput k m c t ∧
  upperEntries k m c t = CounterLeaderCollision.upperEntries k m c t ∧
  upperResiduals k m c t = CounterLeaderCollision.upperResiduals k m c t

def CounterSource : Prop :=
  (∀ n m c e t u : Nat,
    CounterSourceTheorem.commonTail n m c e ≤ t →
    CounterSourceTheorem.commonTail n m c e ≤ u →
    (entries n c t).map Prod.fst = (List.range (n+1)).reverse.map (fun i => i+3) ∧
    Even (leader n c t) ∧
    (count (n+3) c t : Int) = (leader n c t / 2 : Nat) + 1 - ((c+1)/2 : Nat) +
      ((residuals n c t).sum : Int) ∧
    leader n c t < 2 * count (n+3) c t ∧
    4 * count (n+3) c t < 3 * leader n c t ∧
    (leader n c t = leader m e u → c = e) ∧
    (m ≤ n → leader n c t = leader m e u →
      u = alignedInput (n-m) m c t ∧
      (count (n+3) c t : Int) - (count (m+3) e u : Int) =
        ((upperResiduals (n-m) m c t).sum : Int) ∧
      (∀ p ∈ upperEntries (n-m) m c t, m+3 < p.1) ∧
      (m < n → count (m+3) e u < count (n+3) c t)) ∧
    (count (n+3) c t < count (m+3) e u ↔
      leader n c t < leader m e u ∨ (leader n c t = leader m e u ∧ n < m)) ∧
    (count (n+3) c t = count (m+3) e u ↔ leader n c t = leader m e u ∧ n = m)) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    CounterSourceTheorem.commonTail p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    CounterResidualDivergence.threshold p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat =>
    CounterFixedShiftComparison.threshold p.1 p.2.1 p.2.2.1 p.2.2.2)


def Full : Prop := LadderCalibration ∧ UpperCalibration ∧ CounterSource
end LogicLineages.StandardControlCurrent.CounterExpansionTargets
