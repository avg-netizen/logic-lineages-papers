module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWeakeningAccessibilityTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWeakeningAccessibilityProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedPrimaryWeakening

theorem actualWeakeningAccessibilityForward : NumberedWeakeningAccessibilityTargets.ActualWeakeningAccessibilityForward := by
  intro n arity symbols S hc above Gamma sigma q hq hacc
  let R := PositivePath (QuotientEdge n arity symbols S above Gamma)
  let T := PositivePath (QuotientEdge n arity symbols S above (sigma :: Gamma))
  have transfer : ∀ code, Acc (fun y x => R x y) code →
      ∀ p : Packed (Fin n) arity Gamma, InUniverse symbols S p.2 → representativeCode symbols S p = code →
      Acc (fun y x => T x y) (representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) p)) := by
    intro code ha
    induction ha with
    | intro code h ih =>
      intro p hp he
      refine Acc.intro _ ?_
      intro y hy
      obtain ⟨r,hr,her,hpath⟩ := NumberedQuotientWeakeningProof.actualPositiveWeakeningReflection
        n arity symbols S hc above Gamma sigma p hp y hy
      rw [he] at hpath
      exact her ▸ ih (representativeCode symbols S r) hpath r hr rfl
  exact transfer _ hacc q hq rfl

theorem actualWeakeningAccessibilityBackward : NumberedWeakeningAccessibilityTargets.ActualWeakeningAccessibilityBackward := by
  intro n arity symbols S hc above Gamma sigma q hq hacc
  let R := PositivePath (QuotientEdge n arity symbols S above Gamma)
  let T := PositivePath (QuotientEdge n arity symbols S above (sigma :: Gamma))
  have transfer : ∀ code, Acc (fun y x => T x y) code →
      ∀ p : Packed (Fin n) arity Gamma, InUniverse symbols S p.2 →
        representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) p) = code →
      Acc (fun y x => R x y) (representativeCode symbols S p) := by
    intro code ha
    induction ha with
    | intro code h ih =>
      intro p hp he
      refine Acc.intro _ ?_
      intro y hy
      obtain ⟨count,hpos,hcount⟩ := (NumberedQuotientPathsProof.positiveClosure n arity symbols S above Gamma _ _).mp hy
      obtain ⟨r,hr,her,htrace⟩ := NumberedQuotientPathsProof.liftPath symbols S hc above Gamma hcount p hp rfl
      have hpr : R (representativeCode symbols S p) (representativeCode symbols S r) := her.symm ▸ hy
      have hstep := NumberedTraceRenamingProof.actualPositiveQuotientRenaming n arity symbols S hc above Gamma
        (sigma :: Gamma) (Renaming.weaken Gamma sigma) p r hp hr hpr
      rw [he] at hstep
      exact her ▸ ih (representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) r)) hstep r hr rfl
  exact transfer _ hacc q hq rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWeakeningAccessibilityProof
