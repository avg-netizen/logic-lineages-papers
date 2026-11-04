module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSupportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRenamingSupport

theorem finiteMarkSupport {Symbol : Type} {arity : Symbol → Nat} (label : Nat)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (P : VariablePredicate Gamma) (r : AuxTerm Symbol arity Gamma tau), finiteMark label q = some r →
      (supports P q ↔ supports P r) := by
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  case lam body ih =>
    intro P r h
    cases hm : finiteMark label body with
    | none => simp [finiteMark,hm] at h
    | some body' =>
      simp only [finiteMark,hm,Option.map_some,Option.some.injEq] at h
      subst r
      exact ih (liftPredicate P) body' hm
  case ordinary f base ih =>
    intro P r h
    simp only [finiteMark,Option.some.injEq] at h
    subst r
    simp [supports,supportsArguments]
  all_goals first | trivial | (intros; simp_all [finiteMark])

theorem actualFiniteMarkSupport : NumberedMarkSupportTargets.ActualFiniteMarkSupport := by
  intro Symbol arity Gamma P label tau q r h
  exact finiteMarkSupport label q P r h

theorem actualPrimitiveMarkSupport : NumberedMarkSupportTargets.ActualPrimitiveMarkSupport := by
  intro Symbol arity Gamma P q r h
  cases h with
  | mk label q r hm => exact finiteMarkSupport label q P r hm

theorem actualPrimitiveMultisetSupport : NumberedMarkSupportTargets.ActualPrimitiveMultisetSupport := by
  intro Symbol arity Gamma P source target h hs r hr
  obtain ⟨kept,removed,inserted,hsource,htarget,hn,hw⟩ := h
  have hm := htarget.mem_iff.mp hr
  rcases List.mem_append.mp hm with hk | hi
  · exact hs r (hsource.mem_iff.mpr (List.mem_append.mpr (Or.inl hk)))
  · obtain ⟨q,hq,hmark⟩ := hw r hi
    exact (actualPrimitiveMarkSupport Symbol arity Gamma P q r hmark).mp
      (hs q (hsource.mem_iff.mpr (List.mem_append.mpr (Or.inr hq))))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSupportProof
