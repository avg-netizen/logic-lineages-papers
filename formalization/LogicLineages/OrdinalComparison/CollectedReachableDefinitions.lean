module
public import LogicLineages.OrdinalComparison.CollectedAffineBandDefinitions
public import LogicLineages.OrdinalComparison.CollectedNonlinearBandDefinitions
public import LogicLineages.OrdinalComparison.CommonBandOrbitDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def collectedAtomThreshold (rho : NONote) : CollectedPositiveNF → Nat
  | .mk c b .nil => collectedAffineThreshold rho c b
  | .mk c b (.cons sigma A a rest) =>
      collectedNonlinearThreshold rho c b (.cons sigma A a rest)

mutual
  def collectedReachableTags : CollectedPositiveNF → List (NONote × CollectedPositiveNF)
    | .mk _ _ tags => collectedNestedTags tags
  def collectedNestedTags : CollectedPositiveTags → List (NONote × CollectedPositiveNF)
    | .nil => []
    | .cons rho A _ rest => (rho,A) :: (collectedReachableTags A ++ collectedNestedTags rest)
end

mutual
  def collectedOneInputThreshold : CollectedPositiveNF → Nat
    | .mk _ _ tags => collectedTagsOneInputThreshold tags
  def collectedTagsOneInputThreshold : CollectedPositiveTags → Nat
    | .nil => 1
    | .cons rho A _ rest => max (collectedAtomThreshold rho A)
        (max (collectedOneInputThreshold A) (collectedTagsOneInputThreshold rest))
end

def collectedFamilyTags (forms : List CollectedPositiveNF) : List (NONote × CollectedPositiveNF) :=
  forms.flatMap collectedReachableTags

def collectedFamilyThreshold (forms : List CollectedPositiveNF) : Nat :=
  forms.foldr (fun A bound => max (collectedOneInputThreshold A) bound) 1

end LogicLineages.OrdinalComparison
