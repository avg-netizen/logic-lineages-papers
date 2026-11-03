module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparisonTargets
public import LogicLineages.OrdinalComparison.SourceSpecialApplicationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedPrefixProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening
open SourceExtendedComparison

theorem prefixRefl {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : Arguments Symbol arity Gamma types) : Prefix args args := by
  induction types with
  | nil => cases args; exact .nil .nil
  | cons tau types ih =>
    cases args with
    | cons q rest => exact .cons q rest rest (ih rest)

theorem prefixSubset {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    {pre : Arguments Symbol arity Gamma xs} {whole : Arguments Symbol arity Gamma ys}
    (h : Prefix pre whole) : ∀ p∈argumentList pre,p∈argumentList whole := by
  induction h with
  | nil whole => intro p hp; cases hp
  | cons q a b hp ih =>
    intro p hm
    rcases List.mem_cons.mp hm with he | ht
    · subst p; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih p ht)

theorem prefixWholeSharp {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes preTypes : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (pre : Arguments Symbol arity Gamma preTypes)
    (h : Prefix pre extras) (tau : Ty) :
    Sharp Symbol arity Gamma (.marked f tau base sourceTypes extras) (.marked f tau base preTypes pre) := by
  apply Sharp.marked f tau base base sourceTypes extras preTypes pre
  · exact SourceSharpeningReflexivityProof.reflexiveArguments base
  · exact SourceSharpeningReflexivityProof.extrasFromArguments f base extras pre pre
      (SourceSharpeningReflexivityProof.reflexiveArguments pre) (prefixSubset h)

theorem copiesSelf {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (types : List Ty) :
    PrefixCopies f base extras (selfArguments f base sourceTypes extras types) := by
  induction types with
  | nil => exact .nil
  | cons tau types ih => exact .cons tau sourceTypes types extras _ (prefixRefl extras) ih

theorem copiesSharp {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (copies : Arguments Symbol arity Gamma types)
    (h : PrefixCopies f base extras copies) : ExtrasSharp Symbol arity Gamma f base sourceTypes extras copies := by
  induction h with
  | nil => exact .nil _ _ _ _
  | cons tau preTypes restTypes pre rest hp hr ih =>
    exact .cons f base sourceTypes extras tau restTypes _ rest
      (.whole f base sourceTypes extras tau _ (prefixWholeSharp f base extras pre hp tau)) ih

theorem copiesExpansion {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (copies : Arguments Symbol arity Gamma types)
    (h : PrefixCopies f base extras copies) (tau : Ty) :
    Sharp Symbol arity Gamma (.marked f tau base sourceTypes extras)
      (.marked f tau base (sourceTypes++types) (appendArguments extras copies)) := by
  apply Sharp.marked f tau base base sourceTypes extras _ _
  · exact SourceSharpeningReflexivityProof.reflexiveArguments base
  · apply SourceSharpeningApplicationSupportProof.appendTargets
    · exact SourceSharpeningReflexivityProof.extrasFromArguments f base extras extras extras
        (SourceSharpeningReflexivityProof.reflexiveArguments extras) (fun p hp => hp)
    · exact copiesSharp f base extras copies h

theorem tupleCopies {Symbol : Type} {arity : Symbol → Nat} {Gamma typesQ typesS types : List Ty}
    (f : Head Symbol) (baseQ baseS : Arguments Symbol arity Gamma (headArguments arity f))
    (extrasQ : Arguments Symbol arity Gamma typesQ) (extrasS : Arguments Symbol arity Gamma typesS)
    (output : Ty) (hQS : Sharp Symbol arity Gamma (.marked f output baseQ typesQ extrasQ) (.marked f output baseS typesS extrasS))
    (copies : Arguments Symbol arity Gamma types) (h : PrefixCopies f baseS extrasS copies) :
    ArgumentsSharp Symbol arity Gamma (selfArguments f baseQ typesQ extrasQ types) copies := by
  induction h with
  | nil => exact .nil
  | cons tau preTypes restTypes pre rest hp hr ih =>
    apply ArgumentsSharp.cons _ _ _ _
    · exact SourceSharpeningCompositionProof.transitivity Symbol arity Gamma tau _ _ _
        (SourceSharpeningReflexivityProof.retagging Symbol arity Gamma f output tau baseQ baseS
          typesQ typesS extrasQ extrasS hQS) (prefixWholeSharp f baseS extrasS pre hp tau)
    · exact ih

theorem selfApplicationRefinement {Symbol : Type} {arity : Symbol → Nat} {Gamma sourceTypes : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Gamma (headArguments arity f))
    (extras : Arguments Symbol arity Gamma sourceTypes) (sigma tau : Ty) (types : List Ty)
    (suffix : sigma=arrows types tau) (r : MarkedTerm Symbol arity Gamma tau)
    (h : applyOriginalWith (.marked f sigma base sourceTypes extras) (fun v => .var v)
      (selfArguments f base sourceTypes extras types) suffix=some r) :
    Sharp Symbol arity Gamma (.marked f tau base sourceTypes extras) r := by
  cases types with
  | nil =>
    cases suffix
    have hr : MarkedTerm.marked f tau base sourceTypes extras=r := Option.some.inj
      ((SourceSpecialApplicationProof.emptySpecialApplication Symbol arity Gamma tau _).symm.trans h)
    subst r
    exact SourceSharpeningReflexivityProof.reflexiveTerm _
  | cons upsilon types =>
    have hb := SourceMarkedBindingProof.markedSubstitutionIdentity.2 Symbol arity Gamma _ base
    have he := SourceMarkedBindingProof.markedSubstitutionIdentity.2 Symbol arity Gamma sourceTypes extras
    simp only [selfArguments,applyOriginalWith,hb,he] at h
    have hr : MarkedTerm.marked f tau base _
        (appendArguments extras (.cons (.marked f upsilon base sourceTypes extras)
          (selfArguments f base sourceTypes extras types)))=r := Option.some.inj h
    subst r
    exact copiesExpansion f base extras _ (copiesSelf f base extras (upsilon::types)) tau

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedPrefixProof
