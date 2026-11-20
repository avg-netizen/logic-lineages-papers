module
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.PositiveArithmeticTransformsProof
public section
namespace LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.Source
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators PositiveArithmeticOperatorsSupportProof
open PositiveArithmeticTransformsProof SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowComputabilityFormulaTargets NumberedWindowComputabilityReading

private theorem allNat {α : Type} (phi : language.Formula (α ⊕ Fin 1))
    (P : Nat → Prop) (env : α → Nat) :
    realize P (allOne phi) env ↔ ∀ n : Nat, realize P phi (Sum.elim env fun _ => n) := by
  rw [allOneTruth]
  constructor
  · intro h n
    exact h (fun _ => n)
  · intro h xs
    have H : xs = fun _ => xs 0 := by
      funext i
      rw [Subsingleton.elim i (0 : Fin 1)]
    rw [H]
    exact h (xs 0)

private theorem acceptsTruth {α : Type} (p : Program 3) (q u v : OrdinaryArithmetic.Term α)
    (P : Nat → Prop) (env : α → Nat) :
    realize P (accepts p q u v) env ↔ graphHolds p (q.realize env) (u.realize env) (v.realize env) := by
  rw [accepts, embeddingTruth, OrdinaryArithmeticProgramProof.appliedProgramGraphTruth]
  rfl

theorem exact_TypeFormulaReading : TypeFormulaReading := by
  intro p τ
  induction τ with
  | ground =>
    intro α q P env
    rw [formula, predicateTruth, tagTermTruth]
    rfl
  | arrow σ τ ihσ ihτ =>
    intro α q P env
    unfold formula holds
    simp only [allNat, generalImpTruth, acceptsTruth, ihσ, ihτ,
      FirstOrder.Language.Term.realize_relabel, FirstOrder.Language.Term.realize, Sum.elim_inl,
      Sum.elim_inr, Function.comp_def]

#print axioms exact_TypeFormulaReading
end LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaChecks
