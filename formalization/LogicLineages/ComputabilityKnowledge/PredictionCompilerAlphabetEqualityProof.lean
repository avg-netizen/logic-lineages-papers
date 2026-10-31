module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityProof
open Turing Turing.PartrecToTM2 PredictionCompilerSupport PredictionCompilerTapeSupport
open PredictionCompilerAlphabetEquality PredictionCompilerAlphabetEqualityTargets

private theorem symbols_all (s : Store) : s ∈ symbols := by
  cases s with | none => simp [symbols] | some a => cases a <;> simp [symbols]

theorem completeWorkAlphabet : CompleteWorkAlphabet := by
  rintro ⟨b, f⟩
  simp only [workSymbols, List.mem_flatMap, List.mem_map]
  refine ⟨b, by cases b <;> simp, f .main, symbols_all _, f .rev, symbols_all _,
    f .aux, symbols_all _, f .stack, symbols_all _, ?_⟩
  have hf : slots (f .main) (f .rev) (f .aux) (f .stack) = f := by
    funext k
    cases k <;> rfl
  exact congrArg (fun g : K' → Store => (b, g)) hf

theorem exactWorkSymbolComparison : ExactWorkSymbolComparison := by
  intro a b
  constructor
  · intro h
    simp only [workEq, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨hb, hm⟩, hr⟩, ha⟩, hs⟩ := h
    apply Prod.ext hb
    funext k
    cases k with
    | main => exact hm
    | rev => exact hr
    | aux => exact ha
    | stack => exact hs
  · rintro rfl
    simp [workEq]

theorem exactInputFunctionComparison : ExactInputFunctionComparison := by
  intro β compare hc f g
  constructor
  · intro h
    funext a s
    apply (hc (f a s) (g a s)).1
    exact (List.all_eq_true.mp ((List.all_eq_true.mp h) a (completeWorkAlphabet a))) s (symbols_all s)
  · rintro rfl
    apply List.all_eq_true.mpr
    intro a _
    apply List.all_eq_true.mpr
    intro s _
    exact (hc (f a s) (f a s)).2 rfl

/-- Concrete finite-coordinate Boolean comparison, not classical equality. -/
def workDecidableEq : DecidableEq TapeAlphabet := fun a b =>
  decidable_of_iff (workEq a b = true) (exactWorkSymbolComparison a b)

end LogicLineages.ComputabilityKnowledge.PredictionCompilerAlphabetEqualityProof
