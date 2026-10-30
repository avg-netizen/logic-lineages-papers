module
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceDefinitions
public import LogicLineages.OrdinalComparison.CollectedReachableDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

mutual
  def collectedFormClosure : CollectedPositiveNF → List CollectedPositiveNF
    | .mk c b tags => .mk c b tags :: collectedTagFormClosure tags
  def collectedTagFormClosure : CollectedPositiveTags → List CollectedPositiveNF
    | .nil => []
    | .cons _ A _ rest => collectedFormClosure A ++ collectedTagFormClosure rest
end

def collectedFiniteClosure (forms : List CollectedPositiveNF) : List CollectedPositiveNF :=
  CollectedPositiveNF.mk 0 0 .nil :: forms.flatMap collectedFormClosure

end LogicLineages.OrdinalComparison
