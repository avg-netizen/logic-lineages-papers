module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierTargets
open NormalForm PlainFrontier

def ActualAdvance : Prop := ∀ s : State, Plain s → (Meaning (advance s) ↔ Meaning s)
def IteratedPlain : Prop := ∀ (n : Nat) (s : State), Plain s → Plain (run n s)
def ActualIteration : Prop := ∀ (n : Nat) (s : State), Plain s → (Meaning (run n s) ↔ Meaning s)

def StrictRankBound : Prop := ∀ (n M : Nat) (s : State),
  (∀ p ∈ s.2, (PlainBranchProvenance.nonlinearNames p).card ≤ M) →
  ∀ p ∈ (run n s).2, (PlainBranchProvenance.nonlinearNames p).card + n ≤ M

def LiteralFuelBound : Prop := ∀ p : Formula,
  (PlainBranchProvenance.nonlinearNames p).card < fuel p

def FrontierExhaustion : Prop := ∀ p : Formula, (run (fuel p) (initial p)).2 = []

def ActualDecision : Prop := ∀ p : Formula, MaximalPlainBranch.isPlain p = true →
  (answer p = true ↔ PlainLinearCleanup.Satisfiable p)

def ExactRejectingDecision : Prop :=
  (∀ p : Formula, (PlainFrontier.decide p).isSome = MaximalPlainBranch.isPlain p) ∧
  ∀ p : Formula, MaximalPlainBranch.isPlain p = true → ∀ b : Bool,
    PlainFrontier.decide p = some b ↔ (PlainLinearCleanup.Satisfiable p ↔ b = true)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierTargets
