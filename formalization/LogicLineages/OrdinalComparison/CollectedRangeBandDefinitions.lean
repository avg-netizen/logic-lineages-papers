module
public import LogicLineages.OrdinalComparison.CollectedNonlinearBandDefinitions
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Conservative effective source cell threshold; the extra two is the actual
omega norm used to reuse the proved atom band, not a truncation convention. -/
def collectedRangeThreshold : CollectedPositiveNF → Nat
  | .mk c b tags => max 4 (max (2+c+b) (2*collectedCoefficientSum tags+1))

def encodedCollectedRangeThreshold (n : Nat) : Nat :=
  let p := n.unpair
  let q := p.2.unpair
  max 4 (max (2+p.1+q.1) (2*(encodedCollectedThresholdData q.2).1+1))

end LogicLineages.OrdinalComparison
