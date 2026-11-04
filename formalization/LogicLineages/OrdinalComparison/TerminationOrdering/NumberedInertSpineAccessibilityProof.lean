module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineAccessibilityProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowTraces NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedInertSpine

theorem actualTraceInertBound : NumberedInertSpineAccessibilityTargets.ActualTraceInertBound := by
  intro Symbol arity symbols S above Gamma count q r h
  induction h with
  | equivalent he =>
    intro hb
    obtain ⟨hshape, hdepth⟩ := NumberedInertSpineProof.actualPrimaryInertInvariant Symbol arity symbols S Gamma _ _ he
    exact ⟨hshape.mp hb, by omega⟩
  | raw q r hs =>
    intro hb
    obtain ⟨hr, hlt⟩ := NumberedInertSpineProof.actualStepInertDecrease Symbol arity symbols S above Gamma _ q r hs hb
    exact ⟨hr, by change inertRank r + 1 ≤ inertRank q; omega⟩
  | trans h1 h2 ih1 ih2 =>
    intro hb
    obtain ⟨hm, hbound1⟩ := ih1 hb
    obtain ⟨hr, hbound2⟩ := ih2 hm
    exact ⟨hr, by omega⟩

theorem actualQuotientInertAccessibility : NumberedInertSpineAccessibilityTargets.ActualQuotientInertAccessibility := by
  intro n arity symbols S hc above Gamma tau q hq hb
  have main : ∀ depth : Nat, ∀ q : AuxTerm (Fin n) arity Gamma tau,
      inertRank q = depth → InUniverse symbols S q → InertSpine q →
      Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
        (representativeCode symbols S ⟨tau,q⟩) := by
    intro depth
    induction depth using Nat.strong_induction_on with
    | h depth ih =>
      intro q he hq hb
      refine Acc.intro _ ?_
      intro y hy
      obtain ⟨r, hr, hcode, count, hpos, htrace⟩ :=
        NumberedInverseApplicationAccessibilityProof.actualTypedSuccessorWitness
          n arity symbols S hc above Gamma tau q y hq hy
      have hpacked := (NumberedWindowTracesProof.typedPresentation (Fin n) arity symbols S above Gamma
        tau count q r).mpr htrace
      obtain ⟨hbr, hbound⟩ := actualTraceInertBound (Fin n) arity symbols S above Gamma count
        ⟨tau,q⟩ ⟨tau,r⟩ hpacked hb
      change inertRank r + count ≤ inertRank q at hbound
      have hlt : inertRank r < depth := by omega
      exact hcode ▸ ih (inertRank r) hlt r rfl hr hbr
  exact main (inertRank q) q rfl hq hb

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineAccessibilityProof
