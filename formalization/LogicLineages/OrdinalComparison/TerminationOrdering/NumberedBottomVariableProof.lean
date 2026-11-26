module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedUniverseBindingTargets NumberedPrimarySubstitution NumberedBottomVariable

theorem actualLiftBottomOrVariable : NumberedBottomVariableTargets.ActualLiftBottomOrVariable := by
  intro Symbol arity Gamma Delta sigma theta ht tau v
  cases v with
  | here => exact Or.inr ⟨.here,rfl⟩
  | there v =>
    rcases ht v with hb | ⟨w,hw⟩
    · exact Or.inl (by simp only [liftSubstitution,hb,rename])
    · exact Or.inr ⟨.there w,by simp only [liftSubstitution,hw,rename,Renaming.weaken]⟩

theorem actualBottomOrVariableGood : NumberedBottomVariableTargets.ActualBottomOrVariableGood := by
  intro Symbol arity K H Gamma Delta theta ht tau v hk
  rcases ht v with hb | ⟨w,hw⟩
  · rw [hb]
    exact ⟨hk,trivial⟩
  · rw [hw]
    exact ⟨hk,trivial⟩

theorem actualSingleBottomOrVariable : NumberedBottomVariableTargets.ActualSingleBottomOrVariable := by
  intro Symbol arity Gamma sigma tau v
  cases v with
  | here => exact Or.inl rfl
  | there v => exact Or.inr ⟨v,rfl⟩

theorem finiteMarkInverse {Symbol : Type} {arity : Symbol → Nat} (label : Nat)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      BottomOrVariable theta → ∀ r : AuxTerm Symbol arity Delta tau,
      finiteMark label (substitute q theta) = some r →
      ∃ q' : AuxTerm Symbol arity Gamma tau,
        finiteMark label q = some q' ∧ substitute q' theta = r := by
  induction q using AuxTerm.rec (motive_2 := fun _ _ _ => True)
  case var v =>
    intro Delta theta ht r hm
    rcases ht v with hb | ⟨w,hw⟩
    · simp [substitute,hb,finiteMark] at hm
    · simp [substitute,hw,finiteMark] at hm
  case lam body ih =>
    intro Delta theta ht r hm
    simp only [substitute,finiteMark,Option.map_eq_some_iff] at hm
    obtain ⟨body',hb,hr⟩ := hm
    obtain ⟨body'',hm,he⟩ := ih _ (liftSubstitution theta)
      (actualLiftBottomOrVariable Symbol arity _ _ _ theta ht) body' hb
    refine ⟨.lam body'',?_,?_⟩
    · simp only [finiteMark,hm,Option.map_some]
    · simpa only [substitute,he] using hr
  case ordinary f base ih =>
    intro Delta theta ht r hm
    simp only [substitute,finiteMark,Option.some.injEq] at hm
    exact ⟨.numbered label f (Source.SourceMarkedSyntax.headResult f) base [] .nil,rfl,hm⟩
  all_goals first | trivial | (intros; simp_all [substitute,finiteMark])

theorem actualFiniteMarkInverse : NumberedBottomVariableTargets.ActualFiniteMarkInverse := by
  intro Symbol arity Gamma Delta theta ht label tau q r hm
  exact finiteMarkInverse label q Delta theta ht r hm

theorem actualPrimitiveMarkInverse : NumberedBottomVariableTargets.ActualPrimitiveMarkInverse := by
  intro Symbol arity Gamma Delta theta ht q r hm
  rcases q with ⟨tau,q⟩
  cases hm with
  | mk label _ r hm =>
    obtain ⟨q',hq',he⟩ := finiteMarkInverse label q Delta theta ht r hm
    exact ⟨⟨tau,q'⟩,.mk label q q' hq',congrArg (fun r => (⟨tau,r⟩ : Packed Symbol arity Delta)) he⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableProof
