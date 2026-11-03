module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening PrefixSourceComposition
open PrefixTupleCompositionSupportProof

theorem actualNonemptyPrefixTupleComposition : PrefixTupleCompositionTargets.ActualNonemptyPrefixTupleComposition := by
  intro Symbol arity Gamma Delta f base extraTypes extras sigma middle upsilon tau firstTypes restTypes q
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) generalizing middle firstTypes with
  | var v =>
    intro env first secondHead secondRest H hc hd hs kt fullSuffix intermediate r hfirst hsecond
    cases first with
    | nil => cases hs; exact emptyFirst f base extras _ tau (.var v) env _ H hd kt intermediate r hfirst hsecond
    | cons a rest => cases hfirst
  | @lam Omega sigma bodyType body ih =>
    intro env first secondHead secondRest H hc hd hs kt fullSuffix intermediate r hfirst hsecond
    cases first with
    | nil => cases hs; exact emptyFirst f base extras _ tau (.lam body) env _ H hd kt intermediate r hfirst hsecond
    | cons a rest =>
      obtain ⟨hdom,hcod⟩ := Ty.arrow.inj hs
      cases hdom
      cases hcod
      cases hc with
      | cons argType preTypes tailTypes pre rest hp hrest =>
        have Hext : ∀ rho (v : Variable (sigma::Omega) rho),PrefixImage f base extras
            (extendEnvironment env (.marked f sigma base preTypes pre) v) := by
          intro rho v
          cases v with
          | here => exact .inr ⟨preTypes,pre,hp,rfl⟩
          | there v => exact H _ v
        exact ih middle _ (extendEnvironment env (.marked f sigma base preTypes pre)) rest secondHead secondRest Hext hrest hd
          rfl kt (Ty.arrow.inj fullSuffix).2 intermediate r hfirst hsecond
  | ordinary g bs ih =>
    intro env first secondHead secondRest H hc hd hs kt fullSuffix intermediate r hfirst hsecond
    cases first with
    | nil => cases hs; exact emptyFirst f base extras _ tau (.ordinary g bs) env _ H hd kt intermediate r hfirst hsecond
    | cons a rest =>
      have hi : MarkedTerm.marked g middle (substituteArguments bs env) _ (.cons a rest)=intermediate := Option.some.inj hfirst
      subst intermediate
      apply Or.inl
      simpa only [applyOriginalWith,SourceMarkedBindingProof.markedSubstitutionIdentity.2,appendArguments,List.append_eq,List.cons_append] using hsecond
  | marked g output bs ets es ihb ihe =>
    intro env first secondHead secondRest H hc hd hs kt fullSuffix intermediate r hfirst hsecond
    cases first with
    | nil => cases hs; exact emptyFirst f base extras _ tau (.marked g _ bs ets es) env _ H hd kt intermediate r hfirst hsecond
    | cons a rest =>
      have hi : MarkedTerm.marked g middle (substituteArguments bs env) _
          (appendArguments (substituteArguments es env) (.cons a rest))=intermediate := Option.some.inj hfirst
      subst intermediate
      simp only [applyOriginalWith,SourceMarkedBindingProof.markedSubstitutionIdentity.2] at hsecond
      rw [markedAppendAssociativity] at hsecond
      apply Or.inl
      simpa only [applyOriginalWith,appendArguments,List.append_eq,List.cons_append] using hsecond
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionProof
