module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedAccessibilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedSubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedAccessibilityProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedUniverseBindingTargets NumberedPrimarySubstitution NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedVariableCount

/-- The actual quotient path lifting theorem supplies the original numeric
successor's confined witness; no code-wide substitution operation is used. -/
theorem actualPositiveSuccessorLift :
    NumberedRankedAccessibilityTargets.ActualPositiveSuccessorLift := by
  intro n arity symbols S hc above Gamma q hq y hp
  obtain ⟨count,hpos,hcount⟩ :=
    (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma _ _).mp hp
  obtain ⟨r,hr,her,htrace⟩ :=
    NumberedQuotientPathsProof.liftPath symbols S hc above Gamma hcount q hq rfl
  exact ⟨r,hr,her,her.symm ▸ hp⟩

theorem actualPositivePathTransGen :
    NumberedRankedAccessibilityTargets.ActualPositivePathTransGen := by
  intro H x y
  constructor
  · intro h
    induction h with
    | step h => exact .single h
    | trans h₁ h₂ ih₁ ih₂ => exact ih₂.trans ih₁
  · intro h
    induction h with
    | single h => exact .step h
    | tail h₁ h₂ ih => exact .trans (.step h₂) ih

theorem actualPositivePathAccessibilityEquivalence :
    NumberedRankedAccessibilityTargets.ActualPositivePathAccessibilityEquivalence := by
  intro H x
  constructor
  · intro ha
    exact Subrelation.accessible (fun {y x} h => PositivePath.step h) ha
  · intro ha
    exact Subrelation.accessible
      (fun {y x} h => (actualPositivePathTransGen H x y).mp h) ha.transGen

/-- Outer induction pays genuine transformed positive paths. Inner strong
induction pays only erased paths, using their strict ORIGINAL variable rank. -/
theorem actualSubstitutionAccessibilityReflection :
    NumberedRankedAccessibilityTargets.ActualSubstitutionAccessibilityReflection := by
  intro n arity symbols S hc above Gamma Delta theta q hq htheta hacc
  let R := PositivePath (QuotientEdge n arity symbols S above Gamma)
  let T := PositivePath (QuotientEdge n arity symbols S above Delta)
  have transfer : ∀ code, Acc (fun y x => T x y) code →
      ∀ measure (p : Packed (Fin n) arity Gamma), InUniverse symbols S p.2 →
        representativeCode symbols S (substitutePacked theta p) = code →
        packedVariableCount p = measure →
        Acc (fun y x => R x y) (representativeCode symbols S p) := by
    intro code ha
    induction ha with
    | intro code h outer =>
      intro measure
      induction measure using Nat.strong_induction_on with
      | h measure inner =>
        intro p hp he hmeasure
        refine Acc.intro _ ?_
        intro y hy
        obtain ⟨r,hr,her,hpr⟩ := actualPositiveSuccessorLift
          n arity symbols S hc above Gamma p hp y hy
        rcases NumberedRankedSubstitutionProof.actualRankedPositiveQuotientSubstitution
          n arity symbols S hc above Gamma Delta theta p r hp hr htheta hpr with
          ⟨hs,ht⟩ | hpath
        · have hrank : packedVariableCount r < measure := by
            rw [← hmeasure]
            exact ht
          have hre : representativeCode symbols S (substitutePacked theta r) = code :=
            hs.symm.trans he
          exact her ▸ inner (packedVariableCount r) hrank r hr hre rfl
        · have hnext : T code (representativeCode symbols S (substitutePacked theta r)) := by
            rw [← he]
            exact hpath
          exact her ▸ outer _ hnext (packedVariableCount r) r hr rfl rfl
  exact transfer _ hacc (packedVariableCount q) q hq rfl rfl

theorem actualSubstitutionEdgeAccessibilityReflection :
    NumberedRankedAccessibilityTargets.ActualSubstitutionEdgeAccessibilityReflection := by
  intro n arity symbols S hc above Gamma Delta theta q hq htheta hacc
  have hp := (actualPositivePathAccessibilityEquivalence
    (QuotientEdge n arity symbols S above Delta) _).mpr hacc
  have hr := actualSubstitutionAccessibilityReflection
    n arity symbols S hc above Gamma Delta theta q hq htheta hp
  exact (actualPositivePathAccessibilityEquivalence
    (QuotientEdge n arity symbols S above Gamma) _).mp hr

theorem actualSingleBottomGoodSubstitution :
    NumberedRankedAccessibilityTargets.ActualSingleBottomGoodSubstitution := by
  intro Symbol arity K H Gamma sigma tau v ht
  cases v with
  | here => exact ⟨ht,trivial⟩
  | there v => exact ⟨ht,trivial⟩

theorem actualSingleBottomAccessibilityReflection :
    NumberedRankedAccessibilityTargets.ActualSingleBottomAccessibilityReflection := by
  intro n arity symbols S hc above Gamma sigma q hq hacc
  exact actualSubstitutionAccessibilityReflection n arity symbols S hc above (sigma :: Gamma) Gamma
    (singleSubstitution (.bottom sigma)) q hq
    (actualSingleBottomGoodSubstitution (Fin n) arity (fun t => t ∈ S)
      (HeadInWindow arity symbols S) Gamma sigma) hacc

theorem actualSingleBottomEdgeAccessibilityReflection :
    NumberedRankedAccessibilityTargets.ActualSingleBottomEdgeAccessibilityReflection := by
  intro n arity symbols S hc above Gamma sigma q hq hacc
  exact actualSubstitutionEdgeAccessibilityReflection n arity symbols S hc above (sigma :: Gamma) Gamma
    (singleSubstitution (.bottom sigma)) q hq
    (actualSingleBottomGoodSubstitution (Fin n) arity (fun t => t ∈ S)
      (HeadInWindow arity symbols S) Gamma sigma) hacc

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedAccessibilityProof
