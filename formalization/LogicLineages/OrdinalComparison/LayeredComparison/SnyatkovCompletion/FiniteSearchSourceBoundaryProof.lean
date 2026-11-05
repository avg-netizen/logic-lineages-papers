module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceSemanticProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceProof
open CommonLayerSyntax FiniteSearchSource

theorem mixed_admission (i j : Nat) (bound : BaseTerm) (hij : i ≠ j) (hi : i ∉ bound.variables) :
    test (boundedOuter i j bound) = true := by
  have hbody : ScopedPhiParameters.test [] (.conjunction (.less (.variable i) bound)
      (.existsNat j (.equal (.variable j) (.phi (.variable i))))) = true := by
    simp [ScopedPhiParameters.test, ScopedPhiParameters.termTest, BaseTerm.variables, freeTerm bound, hij]
  have hg : BoundedSource.guard i (.conjunction (.less (.variable i) bound)
      (.existsNat j (.equal (.variable j) (.phi (.variable i))))) = some bound := by
    simp [BoundedSource.guard, hi]
  unfold boundedOuter
  rw [test_eq]
  simp [hg, scoped_inclusion _ hbody]

theorem mixed_meaning (i j : Nat) (bound : BaseTerm) (hij : i ≠ j) (hi : i ∉ bound.variables) (ν : Nat → Nat) :
    (boundedOuter i j bound).eval ν ↔ 0 < bound.value ν := by
  constructor
  · rintro ⟨n, hn, _⟩
    have hv := BoundedSourceProof.independent_value i bound hi ν n
    have hb : n < bound.value ν := by
      simpa only [SourceFormula.eval, BaseTerm.value, Function.update_self, hv] using hn
    omega
  · intro hb
    refine ⟨0, ?_, ?_⟩
    · simpa only [SourceFormula.eval, BaseTerm.value, Function.update_self,
        BoundedSourceProof.independent_value i bound hi ν 0] using hb
    · refine ⟨Phi 0, ?_⟩
      simp [SourceFormula.eval, BaseTerm.value, Function.update_of_ne hij]

theorem mixedBoundedUnbounded : FiniteSearchSourceTargets.MixedBoundedUnbounded := by
  intro i j bound hij hi
  have ht := mixed_admission i j bound hij hi
  refine ⟨ht, ?_⟩
  intro values
  have hd := (actualDecision values (boundedOuter i j bound)).2 ht true
  have hm := mixed_meaning i j bound hij hi (PlainParameterDecision.valuation values)
  have hd' : FiniteSearchSource.decide values (boundedOuter i j bound) = some true ↔
      (boundedOuter i j bound).eval (PlainParameterDecision.valuation values) := by simpa using hd
  exact hd'.trans hm

theorem unboundedNonlinearBoundary : FiniteSearchSourceTargets.UnboundedNonlinearBoundary := by
  intro i
  simp [test, ScopedPhiParameters.test, ScopedPhiParameters.termTest, BaseTerm.variables, BoundedSource.guard]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchSourceProof
