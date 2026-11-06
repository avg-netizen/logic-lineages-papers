module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairTargets
open PolynomialGraphCompletion

def ExactCounterexample : Prop := ∀ (n mode : Nat) (flag : Bool) (a b : Expr),
  ValidExpr a → ValidExpr b → Fresh n a → Fresh n b →
    (Pair.Closed (Pair.package n mode flag a b) ↔
      ∃ ν : Nat → Nat, (∀ i < n, 0 < ν i) ∧
        ¬(flag = true ∧ Pair.valueRelation mode (a.value ν) (b.value ν)))

/-- Every name used by the literal row matrix is quantified. Original names
are the initial n positive naturals; all following names are fresh natural
nodes. No new free variable or free parameter is introduced. -/
def ExactClosedSupport : Prop := ∀ (n mode : Nat) (flag : Bool) (a b : Expr),
  Fresh n a → Fresh n b →
  let p := Pair.package n mode flag a b
  p.2.1.Nodup ∧ p.2.1 = List.range (n+nodeCount (.add a b)) ∧
    (∀ row ∈ p.2.2.1, ∀ i ∈ rowVariables row, i ∈ p.2.1) ∧
    (∀ i ∈ rowVariables p.2.2.2.1, i ∈ p.2.1) ∧
    (∀ i < n, i ∉ allocated n (.add a b))

def ExactDomainsAndDegree : Prop := ∀ (n mode : Nat) (flag : Bool) (a b : Expr),
  ValidExpr a → ValidExpr b →
  let p := Pair.package n mode flag a b
  3 ≤ p.1.1 ∧ (∀ row ∈ p.2.2.1, RowAllowed p.1.1 row ∧ ∀ ν, RowDomain row ν) ∧
    RowAllowed p.1.1 p.2.2.2.1 ∧ ∀ ν, RowDomain p.2.2.2.1 ν

def LiteralNumericPackage : Prop := ∀ (n mode : Nat) (flag : Bool) (a b : Expr),
  Pair.Code.package (n,mode,flag,a.encode,b.encode) = Pair.package n mode flag a b

def ActualNumericProgram : Prop := Primrec Pair.Code.package
end LogicLineages.OrdinalComparison.LevelTwoCounterexample.PairTargets
