module
public import LogicLineages.OrdinalComparison.MultivariateDirectNormalizeDefinitions
public import LogicLineages.OrdinalComparison.EncodedCollectedMergeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/- A code shadow only: the old scalar coefficient field stores the encoded
new coefficient VECTOR. No equality of the two semantic interpretations is
claimed or used. It reuses the exact existing dictionary-code program. -/
mutual
  def multivariateCollectedShadow : MultivariateCollectedNF → CollectedPositiveNF
    | .mk c b tags => .mk c (multivariateCoefficientCode b) (multivariateCollectedTagsShadow tags)
  def multivariateCollectedTagsShadow : MultivariateCollectedTags → CollectedPositiveTags
    | .nil => .nil
    | .cons rho A a rest => .cons rho (multivariateCollectedShadow A) a
        (multivariateCollectedTagsShadow rest)
end

def encodedMultivariateCoefficientAdd (n m : Nat) : Nat :=
  multivariateCoefficientCode (multivariateCoefficientAdd
    ((Encodable.decode (α := List Nat) n).getD []) ((Encodable.decode (α := List Nat) m).getD []))

def encodedMultivariateVariableCoefficients (i a : Nat) : Nat :=
  multivariateCoefficientCode (multivariateVariableCoefficients i a)

def encodedMultivariateCollectedAdd (n m : Nat) : Nat :=
  let l := n.unpair
  let r := m.unpair
  Nat.pair (l.1+r.1) (Nat.pair
    (encodedMultivariateCoefficientAdd l.2.unpair.1 r.2.unpair.1)
    (encodedCollectedMerge l.2.unpair.2 r.2.unpair.2))

/-- Actual literal-source bottom-up program. Its paired support bit is
derived from the syntax; a closed source call uses the certified evaluator. -/
noncomputable def encodedMultivariateNormalizeStep (n : Nat) (table : List (Nat × Bool)) : Nat × Bool :=
  if n%4=0 then (Nat.pair (n/4) (Nat.pair 0 0),false)
  else if n%4=1 then (Nat.pair 0 (Nat.pair (encodedMultivariateVariableCoefficients (n/4) 1) 0),true)
  else
    let p := (n/4).unpair
    let L := table.getD p.1 (0,false)
    let R := table.getD p.2 (0,false)
    if n%4=2 then (encodedMultivariateCollectedAdd L.1 R.1,L.2 || R.2)
    else if R.2=false then (Nat.pair (encodedMultivariateClosedValue n) (Nat.pair 0 0),false)
    else (Nat.pair 0 (Nat.pair 0 (encodedCollectedCons (Nat.pair p.1 R.1) 1 0)),true)

noncomputable def encodedMultivariateNormalizeTable : Nat → List (Nat × Bool)
  | 0 => []
  | n+1 => encodedMultivariateNormalizeTable n ++ [encodedMultivariateNormalizeStep n (encodedMultivariateNormalizeTable n)]

noncomputable def encodedMultivariateCollectedNormalize (n : Nat) : Nat :=
  ((encodedMultivariateNormalizeTable (n+1)).getD n (0,false)).1

end LogicLineages.OrdinalComparison
