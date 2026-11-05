module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.Targets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.OrdinaryCodeTargets

/-- Every constructor of the unchanged ordinary Mathlib code datatype,
including primitive recursion and minimization, has its actual partial graph. -/
def FullCodeGraphDiophantine : Prop := ∀ c : Nat.Partrec.Code,
  Dioph (graph (Nat.Partrec.Code.eval c))

/-- Existential representation of actual partial-recursive graphs. This is
not a computable procedure extracting polynomials from extensional proofs. -/
def PartrecGraphDiophantine : Prop := ∀ f : Nat →. Nat,
  Nat.Partrec f → Dioph (graph f)

/-- One fixed ordinary code realizes the existing universal evaluator as
an equality of partial functions, retaining both values and undefinedness. -/
def FixedUniversalCode : Prop := ∃ u : Nat.Partrec.Code, ∀ e x : Nat,
  Nat.Partrec.Code.eval u (Nat.pair e x) =
    Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode e) x

-- The final comparator is the unchanged Targets.UniversalEvaluatorDiophantine.
end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.OrdinaryCodeTargets
