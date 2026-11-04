module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedWindowReduction NumberedBottomSpine

theorem actualPrimarySpineInvariant : NumberedBottomSpineTargets.ActualPrimarySpineInvariant := by
  intro Symbol arity symbols S Gamma q r h
  induction h using WindowPrimary.rec (motive_2 := fun _ _ _ _ _ => True)
  case refl => exact ⟨Iff.rfl, rfl⟩
  case symm h ih => exact ⟨ih.1.symm, ih.2.symm⟩
  case trans h1 h2 ih1 ih2 => exact ⟨ih1.1.trans ih2.1, ih1.2.trans ih2.2⟩
  case appFunction q r a h ih => exact ⟨ih.1, congrArg (fun k => k+1) ih.2⟩
  all_goals simp only [BottomSpine, spineDepth] <;> first | trivial | exact fun h => False.elim h

theorem positiveDepth {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (q : AuxTerm Symbol arity Gamma tau) (hb : BottomSpine q) (hn : q ≠ .bottom tau) :
    0 < spineDepth q := by
  cases q <;> simp_all [BottomSpine, spineDepth]

theorem actualStepSpineDecrease : NumberedBottomSpineTargets.ActualStepSpineDecrease := by
  intro Symbol arity symbols S above Gamma tau q r h
  induction h using WindowStep.rec (motive_2 := fun _ _ _ _ _ => True)
  case appFunction q r a h ih =>
    intro hb
    obtain ⟨hr, hlt⟩ := ih hb
    exact ⟨hr, Nat.add_lt_add_right hlt 1⟩
  case bottom q hn =>
    intro hb
    exact ⟨trivial, positiveDepth q hb hn⟩
  all_goals simp only [BottomSpine, spineDepth] <;> first | trivial | exact fun h => False.elim h

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineProof
