module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeTargets
open BooleanGraphCode NonlinearProjectionCompletion

def LiteralTermVariables : Prop := ∀ t : Term, termVariables t.encode = t.variables
def LiteralForest : Prop := ∀ p : Matrix, forest p.encode = (ExpandedBooleanGraph.forest p).encode
def LiteralPredicate : Prop := ∀ (start : Nat) (p : Matrix),
  predicate start p.encode = (ExpandedBooleanGraph.predicate start p).encode
def LiteralFreshAllocation : Prop := ∀ (bound : List Nat) (p : Matrix),
  startFor bound p.encode = ExpandedBooleanGraph.startFor bound p ∧
  allocated bound p.encode = ExpandedBooleanGraph.allocated bound p
/-- No H-free, validity, freshness, valuation or supplied program premise. -/
def LiteralCompiler : Prop := ∀ (bound : List Nat) (p : Matrix),
  compile bound p.encode = (ExpandedBooleanGraph.compile bound p).encode
def ActualPrograms : Prop := Computable termVariables ∧ Computable forest ∧
  Computable₂ predicate ∧ Computable₂ startFor ∧ Computable₂ allocated ∧ Computable₂ compile

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeTargets
