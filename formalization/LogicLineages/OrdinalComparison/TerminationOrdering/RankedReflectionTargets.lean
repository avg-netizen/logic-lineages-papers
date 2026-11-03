module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionTargets
open Source RecursiveComparison RankedTree RankedReflection

/-- FULL simultaneous ORIGINAL-derivation reflection on literal first-order
endpoints. All five actual inductive relations are quantified, including
marked-root comparisons; no supplied smaller-derivation callback occurs. -/
def ActualJointReflection : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (above : Symbol → Symbol → Prop),
  (∀ Gamma (s t : Packed Symbol arity Gamma), RecursiveComparison.Weak Symbol arity above Gamma s t →
    OrdinaryComparison above s t ∧ MarkedComparison above s t) ∧
  (∀ Gamma (s t : Packed Symbol arity Gamma), RecursiveComparison.Strict Symbol arity above Gamma s t →
    StrictComparison above s t) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)), WeakMatch Symbol arity above Gamma ss ts →
    WeakMatching above ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)), StrictMultiset Symbol arity above Gamma ss ts →
    StrictMatching above ss ts) ∧
  (∀ Gamma (ss ts : List (Packed Symbol arity Gamma)), ReplacementMatch Symbol arity above Gamma ss ts →
    Replacements above ss ts)

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionTargets
