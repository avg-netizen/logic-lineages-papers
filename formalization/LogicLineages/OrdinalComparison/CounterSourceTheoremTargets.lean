module
public import LogicLineages.OrdinalComparison.CounterSourceTheoremDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.CounterSourceTheorem.Targets
open CounterLeaderExpansion CounterLeaderCollision

/-- Padding records the initial total norm. The first counted replacement is
exactly the principal suffix replacement at the printed first budget. -/
def ActualKernelStartup : Prop := ∀ d c t : Nat, 1 ≤ d → c+d+1 ≤ t →
  let I := actualSuffixKernelInitial (Ordinal.omega0 ^ (d : Ordinal)) c t
  let Q := actualMaximumPredecessor (Ordinal.omega0 ^ (d : Ordinal)) (Phi t-c)
  c + actualOrdinalNorm I = t ∧
  actualControlledStep (compensatedPrefixControl c) I = Q ∧
  count d c t = actualControlledCount (compensatedPrefixControl c) Q + 1 ∧
  kernel d c t = (Phi^[count d c t]) t

/-- Uniform finite arithmetic for the whole common tail, quantitative residual
tail and fixed-shift tail. No proof or eventual-bound oracle is input. -/
def UniformTailPrograms : Prop :=
  Primrec (fun p : Nat × Nat × Nat × Nat => commonTail p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat => CounterResidualDivergence.threshold p.1 p.2.1 p.2.2.1 p.2.2.2) ∧
  Primrec (fun p : Nat × Nat × Nat × Nat => CounterFixedShiftComparison.threshold p.1 p.2.1 p.2.2.1 p.2.2.2)

/-- Assembled counter clauses for the companion paper07 limit-part convention,
on one explicit uniformly computed common tail. Printed paper08 correspondence
remains pending. Ranks r=n+3,s=m+3 cover all ranks at least three. -/
def WholeCounterLemma : Prop := ∀ n m c e t u : Nat,
  commonTail n m c e ≤ t → commonTail n m c e ≤ u →
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
  (count (n+3) c t = count (m+3) e u ↔ leader n c t = leader m e u ∧ n = m)

end LogicLineages.OrdinalComparison.CounterSourceTheorem.Targets
