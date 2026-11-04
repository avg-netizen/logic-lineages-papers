module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInverseApplicationAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInverseApplicationAccessibilityProof
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedQuotientApplication NumberedWindowTraces

theorem actualTypedSuccessorWitness : NumberedInverseApplicationAccessibilityTargets.ActualTypedSuccessorWitness := by
  intro n arity symbols S hc above Gamma tau q y hq hp
  obtain ⟨count, hpos, hcount⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma
    (representativeCode symbols S ⟨tau,q⟩) y).mp hp
  obtain ⟨⟨rho,r⟩, hr, he, htrace⟩ := NumberedQuotientPathsProof.liftPath symbols S hc above Gamma
    hcount ⟨tau,q⟩ hq rfl
  have ht : tau = rho := NumberedPrimaryEquivalenceProof.traceTypePreservation (Fin n) arity above Gamma
    count ⟨tau,q⟩ ⟨rho,r⟩ (NumberedWindowTracesProof.packedErasure (Fin n) arity symbols S above Gamma
      count ⟨tau,q⟩ ⟨rho,r⟩ htrace)
  cases ht
  exact ⟨r, hr, he, count, hpos,
    (NumberedWindowTracesProof.typedPresentation (Fin n) arity symbols S above Gamma tau count q r).mp htrace⟩

theorem actualInverseApplicationAccessibility :
    NumberedInverseApplicationAccessibilityTargets.ActualInverseApplicationAccessibility := by
  intro n arity symbols S hc above Gamma sigma tau f a hf ha happ
  let R := PositivePath (QuotientEdge n arity symbols S above Gamma)
  have transfer : ∀ code : Nat, Acc (fun successor source => R source successor) code →
      ∀ g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau), InUniverse symbols S g →
        representativeCode symbols S (applicationPacked g a) = code →
        Acc (fun successor source => R source successor) (representativeCode symbols S ⟨.arrow sigma tau,g⟩) := by
    intro code hacc
    induction hacc with
    | intro code h ih =>
      intro g hg he
      refine Acc.intro _ ?_
      intro y hy
      obtain ⟨r, hr, hcode, count, hpos, htrace⟩ :=
        actualTypedSuccessorWitness n arity symbols S hc above Gamma (.arrow sigma tau) g y hg hy
      have hgr : R (representativeCode symbols S ⟨.arrow sigma tau,g⟩)
          (representativeCode symbols S ⟨.arrow sigma tau,r⟩) := hcode.symm ▸ hy
      have hstep := NumberedQuotientApplicationPathsProof.actualPositiveFunctionApplication
        n arity symbols S hc above Gamma sigma tau g r a hg hr ha hgr
      rw [he] at hstep
      exact hcode ▸ ih (representativeCode symbols S (applicationPacked r a)) hstep r hr rfl
  exact transfer _ happ f hf rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInverseApplicationAccessibilityProof
