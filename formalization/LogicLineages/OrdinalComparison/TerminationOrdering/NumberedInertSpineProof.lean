module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedWindowReduction NumberedInertSpine

theorem actualPrimaryInertInvariant : NumberedInertSpineTargets.ActualPrimaryInertInvariant := by
  intro Symbol arity symbols S Gamma q r h
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => exact ⟨Iff.rfl, rfl⟩
  case symm h ih => exact ⟨ih.1.symm, ih.2.symm⟩
  case trans h1 h2 ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2.trans ih2.2⟩
  case appFunction q r a h ih => exact ⟨ih.1, congrArg (fun k => k+2) ih.2⟩
  all_goals simp only [InertSpine, inertRank] <;> first | trivial | exact fun h => False.elim h

theorem positiveRank {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) (hb : InertSpine q) (hn : q ≠ .bottom tau) :
    0 < inertRank q := by
  cases q <;> simp_all [InertSpine, inertRank]

theorem actualStepInertDecrease : NumberedInertSpineTargets.ActualStepInertDecrease := by
  intro Symbol arity symbols S above Gamma tau q r h
  induction h using WindowStep.rec (motive_2 := fun _ _ _ _ _ => True)
  case appFunction q r a h ih =>
    intro hb
    obtain ⟨hr, hlt⟩ := ih hb
    exact ⟨hr, Nat.add_lt_add_right hlt 2⟩
  case bottom q hn =>
    intro hb
    exact ⟨trivial, positiveRank q hb hn⟩
  all_goals simp only [InertSpine, inertRank] <;> first | trivial | exact fun h => False.elim h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineProof
