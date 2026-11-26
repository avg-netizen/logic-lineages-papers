module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableAccessibilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableTraceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRankedAccessibilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableAccessibilityProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedUniverseBindingTargets NumberedPrimarySubstitution NumberedBottomVariable
open NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedWindowTraces

theorem actualPositiveSuccessorInverse :
    NumberedBottomVariableAccessibilityTargets.ActualPositiveSuccessorInverse := by
  intro n arity symbols S hc above Gamma Delta theta q hq ht y hp
  have hgood : GoodSubstitution (fun t => t ∈ S) (HeadInWindow arity symbols S) theta :=
    NumberedBottomVariableProof.actualBottomOrVariableGood (Fin n) arity
      (fun t => t ∈ S) (HeadInWindow arity symbols S) Gamma Delta theta ht
  have himage : InUniverse symbols S (substitutePacked theta q).2 :=
    NumberedUniverseBindingProof.substituteGood (fun t => t ∈ S) (HeadInWindow arity symbols S)
      q.2 Delta theta hq hgood
  obtain ⟨count,hpos,hcount⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Delta _ _).mp hp
  obtain ⟨r,hr,her,htrace⟩ := NumberedQuotientPathsProof.liftPath symbols S hc above Delta
    hcount (substitutePacked theta q) himage rfl
  obtain ⟨q',hsource,he⟩ := NumberedBottomVariableTraceProof.actualTraceInverse
    (Fin n) arity symbols S above Gamma Delta theta ht count q r htrace
  refine ⟨q',NumberedWindowTracesProof.endpoint hc hsource hq,?_,?_⟩
  · rw [he]
    exact her
  · exact (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma _ _).mpr
      ⟨count,hpos,NumberedQuotientPathsProof.countedForward n arity symbols S hc above Gamma
        count q q' hq hsource⟩

theorem actualAccessibilityPreservation :
    NumberedBottomVariableAccessibilityTargets.ActualAccessibilityPreservation := by
  intro n arity symbols S hc above Gamma Delta theta q hq ht hacc
  let R := PositivePath (QuotientEdge n arity symbols S above Gamma)
  let T := PositivePath (QuotientEdge n arity symbols S above Delta)
  have transfer : ∀ code, Acc (fun successor source => R source successor) code →
      ∀ p : Packed (Fin n) arity Gamma, InUniverse symbols S p.2 →
        representativeCode symbols S p = code →
        Acc (fun successor source => T source successor)
          (representativeCode symbols S (substitutePacked theta p)) := by
    intro code ha
    induction ha with
    | intro code h ih =>
      intro p hp he
      refine Acc.intro _ ?_
      intro y hy
      obtain ⟨r,hr,her,hpath⟩ := actualPositiveSuccessorInverse
        n arity symbols S hc above Gamma Delta theta p hp ht y hy
      rw [he] at hpath
      exact her ▸ ih (representativeCode symbols S r) hpath r hr rfl
  exact transfer _ hacc q hq rfl

theorem actualEdgeAccessibilityPreservation :
    NumberedBottomVariableAccessibilityTargets.ActualEdgeAccessibilityPreservation := by
  intro n arity symbols S hc above Gamma Delta theta q hq ht hacc
  have hpositive := (NumberedRankedAccessibilityProof.actualPositivePathAccessibilityEquivalence
    (QuotientEdge n arity symbols S above Gamma) _).mpr hacc
  have himage := actualAccessibilityPreservation n arity symbols S hc above Gamma Delta theta q hq ht hpositive
  exact (NumberedRankedAccessibilityProof.actualPositivePathAccessibilityEquivalence
    (QuotientEdge n arity symbols S above Delta) _).mp himage

theorem actualSingleBottomAccessibilityEquivalence :
    NumberedBottomVariableAccessibilityTargets.ActualSingleBottomAccessibilityEquivalence := by
  intro n arity symbols S hc above Gamma sigma q hq
  constructor
  · intro hacc
    exact actualAccessibilityPreservation n arity symbols S hc above (sigma :: Gamma) Gamma
      (singleSubstitution (.bottom sigma)) q hq
      (NumberedBottomVariableProof.actualSingleBottomOrVariable (Fin n) arity Gamma sigma) hacc
  · exact NumberedRankedAccessibilityProof.actualSingleBottomAccessibilityReflection
      n arity symbols S hc above Gamma sigma q hq

theorem actualSingleBottomEdgeAccessibilityEquivalence :
    NumberedBottomVariableAccessibilityTargets.ActualSingleBottomEdgeAccessibilityEquivalence := by
  intro n arity symbols S hc above Gamma sigma q hq
  constructor
  · intro hacc
    exact actualEdgeAccessibilityPreservation n arity symbols S hc above (sigma :: Gamma) Gamma
      (singleSubstitution (.bottom sigma)) q hq
      (NumberedBottomVariableProof.actualSingleBottomOrVariable (Fin n) arity Gamma sigma) hacc
  · exact NumberedRankedAccessibilityProof.actualSingleBottomEdgeAccessibilityReflection
      n arity symbols S hc above Gamma sigma q hq

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableAccessibilityProof
