module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryDifference.StatementChecks

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder
open GorbowSyntax SixSol20261112.Fuel

/-- A genuine positive additive gap, with the gap bound inside the formula. -/
def lowerBody {ctx : Nat} (a b : Term ctx) : Formula (ctx+1) :=
  .equal (liftTerm b) (.add (liftTerm a) (.succ (.var 0)))
def lower {ctx : Nat} (a b : Term ctx) : Formula ctx := .ex (lowerBody a b)

/-- Complementary nonnegative additive gap, including equality. -/
def upperBody {ctx : Nat} (a b : Term ctx) : Formula (ctx+1) :=
  .equal (liftTerm a) (.add (liftTerm b) (.var 0))
def upper {ctx : Nat} (a b : Term ctx) : Formula ctx := .ex (upperBody a b)

def lowerValue {ctx : Nat} (tag : Nat) (a b : Term ctx) : Formula ctx :=
  .equal (HistoryDifference.pairCall tag a b) (.add (.mul b b) a)
def upperValue {ctx : Nat} (tag : Nat) (a b : Term ctx) : Formula ctx :=
  .equal (HistoryDifference.pairCall tag a b) (.add (.add (.mul a a) a) b)

def pairGraph {ctx : Nat} (tag : Nat) (a b : Term ctx) : Formula ctx :=
  .disj (.conj (lower a b) (lowerValue tag a b)) (.conj (upper a b) (upperValue tag a b))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.HistoryOrder
