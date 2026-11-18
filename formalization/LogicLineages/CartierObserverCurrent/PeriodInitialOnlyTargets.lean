module
public import LogicLineages.OrdinalComparison.CartierOrbitDefinitions
public import LogicLineages.OrdinalComparison.TranslatedRationalDefinitions

@[expose] public section
universe u
namespace LogicLineages.CartierObserverCurrent.PeriodInitialOnly.Targets
open LogicLineages.OrdinalComparison

def InitialResidue : Prop := ∀ u : Nat, 5 ≤ u → ∀ z : ActualPrimitiveRootIndex u,
  (actualTranslatedRationalEmbedding z.val (actualLinkedDifferential u)).coeff (-1) =
    actualResidueTuple u z
end LogicLineages.CartierObserverCurrent.PeriodInitialOnly.Targets
