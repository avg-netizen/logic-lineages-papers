module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedPrimarySubstitution

theorem finiteMarkSubstitute {Symbol : Type} {arity : Symbol → Nat} (label : Nat)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta : List Ty) (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta)
      (r : AuxTerm Symbol arity Gamma tau), finiteMark label q = some r →
      finiteMark label (substitute q rho) = some (substitute r rho) := by
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  case lam body ih =>
    intro Delta rho r h
    cases hm : finiteMark label body with
    | none => simp [finiteMark,hm] at h
    | some body' =>
      simp only [finiteMark,hm,Option.map_some,Option.some.injEq] at h
      subst r
      simp only [substitute,finiteMark,ih _ (liftSubstitution rho) body' hm,Option.map_some]
  case ordinary f base ih =>
    intro Delta rho r h
    simp only [finiteMark,Option.some.injEq] at h
    subst r
    rfl
  all_goals first | trivial | (intros; simp_all [finiteMark])

theorem actualFiniteMarkSubstitution : NumberedMarkSubstitutionTargets.ActualFiniteMarkSubstitution := by
  intro Symbol arity Gamma Delta rho label tau q r h
  exact finiteMarkSubstitute label q Delta rho r h

theorem actualPrimitiveMarkSubstitution : NumberedMarkSubstitutionTargets.ActualPrimitiveMarkSubstitution := by
  intro Symbol arity Gamma Delta rho q r h
  cases h with
  | mk label q r hm =>
    exact PrimitiveMark.mk label (substitute q rho) (substitute r rho)
      (finiteMarkSubstitute label q Delta rho r hm)

theorem actualPrimitiveMultisetSubstitution : NumberedMarkSubstitutionTargets.ActualPrimitiveMultisetSubstitution := by
  intro Symbol arity Gamma Delta rho source target h
  obtain ⟨kept,removed,inserted,hs,ht,hn,hw⟩ := h
  refine ⟨kept.map (substitutePacked rho), removed.map (substitutePacked rho),
    inserted.map (substitutePacked rho), ?_, ?_, ?_, ?_⟩
  · simpa only [List.map_append] using hs.map (substitutePacked rho)
  · simpa only [List.map_append] using ht.map (substitutePacked rho)
  · intro he
    exact hn (List.map_eq_nil_iff.mp he)
  · intro q hq
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hq
    obtain ⟨s,hs,hm⟩ := hw r hr
    exact ⟨substitutePacked rho s,List.mem_map.mpr ⟨s,hs,rfl⟩,
      actualPrimitiveMarkSubstitution Symbol arity Gamma Delta rho s r hm⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkSubstitutionProof
