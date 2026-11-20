module
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityReading
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityFormulaSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticTransforms SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector

def accepts {α : Type} (p : Program 3) (q u v : OrdinaryArithmetic.Term α) : language.Formula α :=
  arithmeticEmbedding.onFormula (OrdinaryArithmetic.applyGraph (OrdinaryArithmetic.graphFormula p)
    (OrdinaryArithmetic.succTerm OrdinaryArithmetic.zeroTerm) ![q,u,v])

def formula (p : Program 3) : (τ : Ty) → {α : Type} → OrdinaryArithmetic.Term α → language.Formula α
  | .ground, _, q => (Positive.predicate (tagTerm false q)).formula
  | .arrow σ τ, _, q =>
    allOne (allOne ((accepts p (q.relabel (fun j => .inl (.inl j))) (.var (.inl (.inr 0))) (.var (.inr 0))).imp
      ((formula p σ (.var (.inl (.inr 0)))).imp (formula p τ (.var (.inr 0))))))

def graphHolds (p : Program 3) (q u v : Nat) : Prop := evaluate p (q ::ᵥ u ::ᵥ v ::ᵥ nil) = 1

def TypeFormulaReading : Prop := ∀ (p : Program 3) (τ : Ty) (α : Type)
    (q : OrdinaryArithmetic.Term α) (P : Nat → Prop) (env : α → Nat),
  realize P (formula p τ q) env ↔
    NumberedWindowComputabilityReading.holds (graphHolds p) P τ (q.realize env)

end LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
