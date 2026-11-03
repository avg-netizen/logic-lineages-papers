module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComposedPrefixSelectionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComposedPrefixSelectionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceUnmarked SourceSharpening PrefixSourceComposition

theorem copiesAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes xs ys : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes)
    (a : Arguments Symbol arity Gamma xs) (b : Arguments Symbol arity Gamma ys)
    (ha : SourceExtendedComparison.PrefixCopies f base extras a)
    (hb : SourceExtendedComparison.PrefixCopies f base extras b) :
    SourceExtendedComparison.PrefixCopies f base extras (appendArguments a b) := by
  induction ha with
  | nil => exact hb
  | cons tau preTypes restTypes pre rest hp hr ih => exact .cons tau preTypes _ pre _ hp ih

theorem actualComposedPrefixSelection : ComposedPrefixSelectionTargets.ActualComposedPrefixSelection := by
  intro Symbol arity above Gamma f base extraTypes extras sigma middle upsilon tau firstTypes restTypes
    q first secondHead secondRest hmem hc hd hs kt fullSuffix intermediate r t hfirst hsecond hrt ht
  have hout := PrefixTupleCompositionProof.actualNonemptyPrefixTupleComposition Symbol arity Gamma Gamma f base extraTypes extras
    sigma middle upsilon tau firstTypes restTypes q (fun v => .var v) first secondHead secondRest
    (fun _ v => .inl ⟨v,rfl⟩) hc hd hs kt fullSuffix intermediate r hfirst hsecond
  rcases hout with hfull | hsharp
  · have he : SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,.marked f tau base extraTypes extras⟩ ⟨tau,t⟩ :=
      .prefixSelect f base extraTypes _ extras (appendArguments first (.cons secondHead secondRest))
        q r t fullSuffix hmem (copiesAppend f base extras first (.cons secondHead secondRest) hc hd) hfull hrt
    exact SourceExtendedEliminationProof.weakUnmarkedConservativity Symbol arity above Gamma tau
      (.marked f tau base extraTypes extras) (.marked f tau base extraTypes extras) t ht
      (SourceSharpeningReflexivityProof.reflexiveTerm _) he
  · exact SourceExtendedEliminationProof.weakUnmarkedConservativity Symbol arity above Gamma tau
      (.marked f tau base extraTypes extras) r t ht hsharp hrt

end LogicLineages.OrdinalComparison.TerminationOrdering.ComposedPrefixSelectionProof
