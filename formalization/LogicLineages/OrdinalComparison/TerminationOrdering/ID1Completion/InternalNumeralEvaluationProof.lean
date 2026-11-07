module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionFreeInitialProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphZeroIntroductionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphSuccessorIntroductionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalRecursionGraph
open SourceComputabilityFormulaSupportProof InternalSourceInversionSupportProof
open InternalRecursionFreeInitialProof InternalGraphCompositionIntroductionProof
open InternalRecursionGraphZeroIntroductionProof InternalRecursionGraphSuccessorIntroductionProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open List.Vector

/-- Numeral substitution preserves the literal counter/parameter input order. -/
theorem numeralInputsCons {n : Nat} {α : Type} (k : Nat) (v : List.Vector Nat n) :
    (fun i => (numeral ((k ::ᵥ v).get i) : OTerm α)) =
      Fin.cons (numeral k) (fun i => numeral (v.get i)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [List.Vector.get_cons_zero, Fin.cons_zero]
  · rw [List.Vector.get_cons_succ, Fin.cons_succ]

/-- Structural induction on the unchanged Program syntax. Its recursion
branch uses meta-level induction on the concrete natural counter, constructing
original-calculus proof trees from the checked literal graph equations. -/
theorem actualOriginalNumeralEvaluation :
    InternalNumeralEvaluationTargets.ActualOriginalNumeralEvaluation := by
  intro body n p
  induction p with
  | zero =>
    intro v α
    rw [actualInitialGraphInstances.1, onEquality]
    exact ⟨Derivation.equalityReflexivity _⟩
  | succ =>
    intro v α
    rw [actualInitialGraphInstances.2.1, onEquality, List.Vector.get_zero]
    exact ⟨Derivation.equalityReflexivity _⟩
  | projection i =>
    intro v α
    rw [actualInitialGraphInstances.2.2, onEquality]
    exact ⟨Derivation.equalityReflexivity _⟩
  | @composition m n f g ihf ihg =>
    intro v α
    apply actualOriginalCompositionIntroduction body m n α []
      (OrdinaryArithmetic.graphFormula f) (fun i => OrdinaryArithmetic.graphFormula (g i))
      (numeral (evaluate (.composition f g) v)) (fun i => numeral (v.get i))
      (fun i => numeral (evaluate (g i) v))
    · simpa only [evaluate, List.Vector.get_ofFn] using
        ihf (List.Vector.ofFn fun i => evaluate (g i) v) α
    · exact fun i => ihg i v α
  | @recursion n f g ihf ihg =>
    intro v α
    have hr : ∀ (k : Nat) (xs : List.Vector Nat n),
        Nonempty (Derivation body []
          (recursion (OrdinaryArithmetic.graphFormula f) (OrdinaryArithmetic.graphFormula g)
            (numeral (evaluate (.recursion f g) (k ::ᵥ xs))) (numeral k)
            (fun i => (numeral (xs.get i) : OTerm α)))) := by
      intro k
      induction k with
      | zero =>
        intro xs
        obtain ⟨df⟩ := ihf xs α
        obtain ⟨dz⟩ := actualOriginalRecursionZeroIntroduction body n α
          (OrdinaryArithmetic.graphFormula f) (OrdinaryArithmetic.graphFormula g)
          (numeral (evaluate f xs)) (fun i => numeral (xs.get i))
        exact ⟨Derivation.implicationElimination dz df⟩
      | succ k ih =>
        intro xs
        apply recursionSuccessorIntroduction []
          (OrdinaryArithmetic.graphFormula f) (OrdinaryArithmetic.graphFormula g)
          (numeral (evaluate (.recursion f g) (k.succ ::ᵥ xs))) (numeral k)
          (numeral (evaluate (.recursion f g) (k ::ᵥ xs))) (fun i => numeral (xs.get i))
        · exact ih xs
        · have dg := ihg (k ::ᵥ evaluate (.recursion f g) (k ::ᵥ xs) ::ᵥ xs) α
          rw [numeralInputsCons, numeralInputsCons] at dg
          exact dg
    rcases v with ⟨values, hvalues⟩
    cases values with
    | nil => simp at hvalues
    | cons k xs =>
      have hxs : xs.length = n := by simpa using hvalues
      have h := hr k ⟨xs, hxs⟩
      unfold recursion at h
      rw [← numeralInputsCons] at h
      exact h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumeralEvaluationProof
