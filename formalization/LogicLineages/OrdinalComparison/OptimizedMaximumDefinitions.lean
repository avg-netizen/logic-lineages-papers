module
public import LogicLineages.OrdinalComparison.ActualMaximumPredecessorDefinitions

@[expose] public section

/-! Literal semantic reference definitions for paper05 thm:maximum.
L is the source M(omega^e,b), not an assumed maximum algorithm. The branch
coefficient and budget/phase rank are fixed before recurrence proofs. These
definitions alone assert neither optimized-recursion correctness nor a
computability certificate for an optimized implementation. -/

namespace LogicLineages.OrdinalComparison

noncomputable def actualLowerPowerMaximum (e : Ordinal.{0}) (b : Nat) : Ordinal :=
  actualMaximumPredecessor (Ordinal.omega0 ^ e) b

noncomputable def actualMaximumDropCoefficient (e r : Ordinal.{0}) (c b : Nat) : Nat := by
  classical
  exact min (if r = 0 then c - 1 else c) (b / (1 + actualOrdinalNorm e))

/-- Phase one is M and phase zero is L, exactly the source termination order. -/
def optimizedMaximumRank (budget phase : Nat) : Nat := 2 * budget + phase

end LogicLineages.OrdinalComparison
