module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PrefixSourceCompositionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening PrefixSourceComposition

/-- ACTUAL composition of two complete tuples, with a nonempty second tuple.
The first tuple may be empty. A consumed prefix variable may block the single
original-spine application: its real output must then be Sharp from the whole
source. No equality of curried and simultaneous evaluation is assumed. -/
def ActualNonemptyPrefixTupleComposition : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma Delta : List Ty) (f : Head Symbol)
    (base : Arguments Symbol arity Delta (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Delta extraTypes) (sigma middle upsilon tau : Ty)
    (firstTypes restTypes : List Ty) (q : MarkedTerm Symbol arity Gamma sigma)
    (env : MarkedSubstitution Symbol arity Gamma Delta)
    (first : Arguments Symbol arity Delta firstTypes)
    (secondHead : MarkedTerm Symbol arity Delta upsilon) (secondRest : Arguments Symbol arity Delta restTypes),
  (∀ rho (v : Variable Gamma rho),PrefixImage f base extras (env v)) →
  SourceExtendedComparison.PrefixCopies f base extras first →
  SourceExtendedComparison.PrefixCopies f base extras (.cons secondHead secondRest) →
  ∀ (firstSuffix : sigma=arrows firstTypes middle)
    (secondSuffix : middle=arrows (upsilon::restTypes) tau)
    (fullSuffix : sigma=arrows (firstTypes++upsilon::restTypes) tau)
    (intermediate : MarkedTerm Symbol arity Delta middle) (r : MarkedTerm Symbol arity Delta tau),
  applyOriginalWith q env first firstSuffix=some intermediate →
  applyOriginalWith intermediate (fun v => .var v) (.cons secondHead secondRest) secondSuffix=some r →
    applyOriginalWith q env (appendArguments first (.cons secondHead secondRest)) fullSuffix=some r ∨
      Sharp Symbol arity Delta (.marked f tau base extraTypes extras) r

end LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionTargets
