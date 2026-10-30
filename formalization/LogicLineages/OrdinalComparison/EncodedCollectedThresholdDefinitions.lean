module
public import LogicLineages.OrdinalComparison.CollectedReachableDefinitions
public import LogicLineages.OrdinalComparison.RawNormCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Simultaneous coefficient-sum/threshold computation on finite tag codes.
Both recursive argument-tag and tail-tag codes are strictly smaller. -/
def encodedCollectedThresholdStep (n : Nat) (table : List (Nat × Nat)) : Nat × Nat :=
  if n=0 then (0,1) else
    let p := n.pred.unpair
    let key := p.1.unpair
    let fields := p.2.unpair
    let argNF := key.2.unpair
    let argFields := argNF.2.unpair
    let arg := table.getD argFields.2 (0,1)
    let rest := table.getD fields.2 (0,1)
    let base := rawNormCode key.1 + argNF.1 + argFields.1
    let atom := if argFields.2=0 then max 4 (base+1) else max 4 (max base (2*arg.1+1))
    (fields.1+rest.1,max atom (max arg.2 rest.2))

def encodedCollectedThresholdTable : Nat → List (Nat × Nat)
  | 0 => []
  | n+1 => encodedCollectedThresholdTable n ++
      [encodedCollectedThresholdStep n (encodedCollectedThresholdTable n)]

def encodedCollectedThresholdData (n : Nat) : Nat × Nat :=
  (encodedCollectedThresholdTable (n+1)).getD n (0,1)

def encodedCollectedThreshold (n : Nat) : Nat :=
  (encodedCollectedThresholdData n.unpair.2.unpair.2).2

def encodedCollectedFamilyThreshold (codes : List Nat) : Nat :=
  codes.foldr (fun n bound => max (encodedCollectedThreshold n) bound) 1

end LogicLineages.OrdinalComparison
