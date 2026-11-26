module

public import LogicLineages.NativeModule.PersistentMarking.ConditionalUpperTargets
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowConfinedRankStageNormProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowCanonicalAddressMapChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalWellFoundedChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowOriginalPresentationChecks
public import LogicLineages.PersistentMarking.NumberedWindowFormulaCalibrationChecks

/-! Proof of the frozen `ConditionalUpperTargets.ConditionalUpper`.

Printed proof (ordinals.tex 319–333) and its carriers:
- well-foundedness: #489 `exact_ConfinedStrictWellFounded` (external route);
- rk_⊐(s) ≤ rk_{R_S}(tr s) = inductive norm of tr(s): #1460 `exact_ConfinedRankBelowTaggedStageNorm`;
- "the arithmetic accessibility proof supplies an ID₁ proof of the individual I-membership of
  tr(s)": hypothesis R1 `IndividualAccessibility`, at the canonical address of tr(s)'s class
  (admitted by `exact_ActualClassAddressSpecification`);
- "the tagged I component has its standalone accessibility norm": the body operator of the
  presentation equals `taggedStep` (`exact_InterpretsEvaluatingPrograms` for any evaluating
  programs, `exact_ActualOperatorAndTerms`), so its stages are those of `taggedStep`;
- "applying the published norm theorem": hypothesis E4 `NormTheorem BH`. -/

@[expose] public section

namespace LogicLineages.PersistentMarking.ConditionalUpperProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.SourcePresentation
open NumberedWindowExternalIDOperators NumberedWindowGuardedNormTargets
open NumberedWindowFormulaCalibrationTargets NumberedWindowPresentationCheckers
open NumberedWindowArithmeticScalarTargets (fixed)
open ConditionalUpperTargets

/-- Body-operator bridge for arbitrary programs evaluating the original checks. -/
theorem bodyOperatorOfEvaluating (S : Spine.Signature) (K : List Ty) (hk : DecisionSourceUniverse.Closed K)
    {i j : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 1}
    {r d : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3}
    (evaluates : Evaluates (checks S.entries (fixed S K)) i j r d) (c : Nat) :
    ExternalOrdinalInterfaceID1Targets.bodyOperator
      (sourceBody (NumberedWindowInternalPresentationTargets.data i j r d) c) = taggedStep S K := by
  have interprets :=
    NumberedWindowFormulaCalibrationChecks.exact_InterpretsEvaluatingPrograms _ i j r d evaluates
  funext P z
  apply propext
  exact ((interprets c P).1 z).trans
    ((NumberedWindowOriginalPresentationChecks.exact_ActualOperatorAndTerms S K hk P).1 z)

theorem exact_ConditionalUpper : ConditionalUpper := by
  intro BH norm individual
  refine ⟨NumberedWindowExternalWellFoundedChecks.exact_ConfinedStrictWellFounded, ?_⟩
  intro S wf q τ typed ordinary
  obtain ⟨hk, Q, hQ, bound, _, taggedLeast, _, _, rankBound⟩ :=
    NumberedWindowConfinedRankStageNormProof.exact_ConfinedRankBelowTaggedStageNorm S q τ typed ordinary
  obtain ⟨_, admitted, _⟩ :=
    NumberedWindowCanonicalAddressMapChecks.exact_ActualClassAddressSpecification S (TypeSupport.support q) []
      τ hk (NumberedWindowSimulationData.classOf ⟨Q, hQ⟩)
  obtain ⟨i, j, r, d, c, evaluates, derivable⟩ := individual S (TypeSupport.support q) hk
  obtain ⟨a, below, staged⟩ := norm _ _ (derivable _ admitted)
  rw [bodyOperatorOfEvaluating S (TypeSupport.support q) hk evaluates c] at staged
  have least := taggedLeast.2 staged
  exact lt_of_le_of_lt ((rankBound (wf.apply q)).trans least) below

#print axioms exact_ConditionalUpper

end LogicLineages.PersistentMarking.ConditionalUpperProof
