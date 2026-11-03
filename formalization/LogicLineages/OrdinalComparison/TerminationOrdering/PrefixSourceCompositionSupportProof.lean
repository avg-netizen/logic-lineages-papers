module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening
open PrefixSourceComposition SourceSharpeningInversionProof

theorem imageShape {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty} {tau : Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma types) (q : MarkedTerm Symbol arity Gamma tau)
    (h : PrefixImage f base extras q) : rootShape ⟨tau,q⟩=0 ∨ rootShape ⟨tau,q⟩=3 := by
  rcases h with ⟨v,rfl⟩ | ⟨preTypes,pre,hp,rfl⟩
  · exact .inl rfl
  · exact .inr rfl

theorem emptyComposition {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta Xi : List Ty} {tau : Ty}
    (q : MarkedTerm Symbol arity Gamma tau) (theta : MarkedSubstitution Symbol arity Gamma Delta)
    (env : MarkedSubstitution Symbol arity Delta Xi) (r : MarkedTerm Symbol arity Xi tau)
    (h : applyOriginalWith (substituteTerm q theta) env .nil rfl=some r) :
    applyOriginalWith q (fun v => substituteTerm (theta v) env) .nil rfl=some r := by
  rw [SuccessfulApplicationPostProof.emptyWith] at h ⊢
  rw [ProtectedApplyBindingProof.substitutionComposition] at h
  exact h

theorem prefixApplication {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes preTypes types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (pre : Arguments Symbol arity Gamma preTypes)
    (hp : SourceExtendedComparison.Prefix pre extras) (copies : Arguments Symbol arity Gamma types)
    (hc : SourceExtendedComparison.PrefixCopies f base extras copies) (sigma tau : Ty)
    (suffix : sigma=arrows types tau) (r : MarkedTerm Symbol arity Gamma tau)
    (h : applyOriginalWith (.marked f sigma base preTypes pre) (fun v => .var v) copies suffix=some r) :
    Sharp Symbol arity Gamma (.marked f tau base sourceTypes extras) r := by
  cases copies with
  | nil =>
    cases suffix
    have he : MarkedTerm.marked f tau base preTypes pre=r := Option.some.inj
      ((SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma tau _).symm.trans h)
    subst r
    exact SourceExtendedPrefixProof.prefixWholeSharp f base extras pre hp tau
  | cons a rest =>
    have hb := SourceMarkedBindingProof.markedSubstitutionIdentity.2 Symbol arity Gamma _ base
    have he := SourceMarkedBindingProof.markedSubstitutionIdentity.2 Symbol arity Gamma preTypes pre
    simp only [applyOriginalWith,hb,he] at h
    have hr : MarkedTerm.marked f tau base _ (appendArguments pre (.cons a rest))=r := Option.some.inj h
    subst r
    apply Sharp.marked f tau base base sourceTypes extras _ _
    · exact SourceSharpeningReflexivityProof.reflexiveArguments base
    · apply SourceSharpeningApplicationSupportProof.appendTargets
      · exact SourceSharpeningReflexivityProof.extrasFromArguments f base extras pre pre
          (SourceSharpeningReflexivityProof.reflexiveArguments pre) (SourceExtendedPrefixProof.prefixSubset hp)
      · exact SourceExtendedPrefixProof.copiesSharp f base extras (.cons a rest) hc

end LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionSupportProof
