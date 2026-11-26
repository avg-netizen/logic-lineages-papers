module
public import LogicLineages.PermittedControl.ActualFiniteGlobalTailTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSyntaxChargeBudget
open MixedSameRankResidue ActualZeroClassReplacement ActualRankedRowColumns
open ActualReadChargeIteration ActualFiniteGlobalTail InnerTerminationTargets

/-- Sufficient budget, not the original exact grouped signed charge. -/
def syntaxBudget (r : Nat) (terms : List WeightedOperand) : Nat :=
  terms.length * 3 ^ r

/-- Total length bound on raw syntax bytes; this program does not
decode or validate any raw operand. -/
def syntaxBudgetCode (r : Nat) (terms : List WeightedCode) : Nat :=
  terms.length * 3 ^ r

/-- Count and ordinary value support have disjoint operand key spaces;
signed cancellation may remove keys but cannot add an occurrence. -/
def ExactDistinctSupportBudget : Prop :=
  ∀ (r : Nat) (c : Int) (raw : List Read),
    let row := rankedRow r c raw
    row.count.support.card + row.value.support.card ≤ raw.length

def ExactChargeBudget : Prop :=
  (∀ (r : Nat) (s : ReadState), stateCharge r s ≤ syntaxBudget r (syntaxOf s)) ∧
  (∀ (r : Nat) (terms : List WeightedOperand), syntaxCharge r terms ≤ syntaxBudget r terms) ∧
  ∀ s : ReadState, stateCharge 0 s = 0

def BudgetCodeExact : Prop :=
  Primrec₂ syntaxBudgetCode ∧
  ∀ (r : Nat) (terms : List WeightedOperand),
    syntaxBudgetCode r (terms.map encodeWeighted) = syntaxBudget r terms

def FullActualSyntaxChargeBudget : Prop :=
  ExactDistinctSupportBudget ∧ ExactChargeBudget ∧ BudgetCodeExact

end LogicLineages.PermittedControl.ActualSyntaxChargeBudget
