module
public import LogicLineages.OrdinalComparison.TerminationOrdering.PrefixTupleCompositionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComposedPrefixSelectionTargets
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceUnmarked

/-- Genuine original-comparison consumer of TWO actual consecutive prefix-copy
applications, final endpoint Unmarked. Both simultaneous-success and actual
Sharp escape are discharged, with no comparison-transitivity premise. -/
def ActualComposedPrefixSelection : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (f : Head Symbol)
    (base : Arguments Symbol arity Gamma (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Gamma extraTypes) (sigma middle upsilon tau : Ty)
    (firstTypes restTypes : List Ty) (q : MarkedTerm Symbol arity Gamma sigma)
    (first : Arguments Symbol arity Gamma firstTypes)
    (secondHead : MarkedTerm Symbol arity Gamma upsilon) (secondRest : Arguments Symbol arity Gamma restTypes),
  (⟨sigma,q⟩ : Packed Symbol arity Gamma)∈argumentList base++argumentList extras →
  SourceExtendedComparison.PrefixCopies f base extras first →
  SourceExtendedComparison.PrefixCopies f base extras (.cons secondHead secondRest) →
  ∀ (firstSuffix : sigma=arrows firstTypes middle)
    (secondSuffix : middle=arrows (upsilon::restTypes) tau)
    (fullSuffix : sigma=arrows (firstTypes++upsilon::restTypes) tau)
    (intermediate : MarkedTerm Symbol arity Gamma middle) (r t : MarkedTerm Symbol arity Gamma tau),
  applyOriginalWith q (fun v => .var v) first firstSuffix=some intermediate →
  applyOriginalWith intermediate (fun v => .var v) (.cons secondHead secondRest) secondSuffix=some r →
  SourceExtendedComparison.Weak Symbol arity above Gamma ⟨tau,r⟩ ⟨tau,t⟩ →
  Unmarked Symbol arity Gamma t →
    RecursiveComparison.Weak Symbol arity above Gamma ⟨tau,.marked f tau base extraTypes extras⟩ ⟨tau,t⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ComposedPrefixSelectionTargets
