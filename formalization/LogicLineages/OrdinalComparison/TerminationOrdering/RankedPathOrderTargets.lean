module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderTargets
open Source RecursiveComparison RankedTree RankedPathOrder

def OriginalRankedRestriction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (above : Symbol → Symbol → Prop) (s t : Tree Symbol arity Gamma),
  (RecursiveComparison.Weak Symbol arity above Gamma (pack s) (pack t) ↔ GreaterEqual above s t) ∧
  (Strict Symbol arity above Gamma (pack s) (pack t) ↔ Greater Symbol arity Gamma above s t)

/-- Literal source06 theorem: confinement imposes no additional condition in
the genuine first-order ranked algebra. The weak closure spells out the
source's type-support restriction; strictness uses its existing ordinary
source definition. Neither relation is defined by the desired equivalence. -/
def ConfinedRankedRestriction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (Gamma : List Ty) (above : Symbol → Symbol → Prop) (s t : Tree Symbol arity Gamma),
  ((RecursiveComparison.Weak Symbol arity above Gamma
      ⟨.ground,Source.SourceMarkedSyntax.embed (ordinary s)⟩
      ⟨.ground,Source.SourceMarkedSyntax.embed (ordinary t)⟩ ∧
    Source.SourceTypeSupport.typeSupport (ordinary t) ⊆ Source.SourceTypeSupport.typeSupport (ordinary s)) ↔ GreaterEqual above s t) ∧
  (LiteralContexts.ConfinedStrict above (ordinary s) (ordinary t) ↔ Greater Symbol arity Gamma above s t)

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedPathOrderTargets
