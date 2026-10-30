module
public import LogicLineages.OrdinalComparison.CollectedPositiveDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

abbrev SignedCollectedRow := List ((NONote × CollectedPositiveNF) × Int)

def collectedDictionaryLength : CollectedPositiveTags → Nat
  | .nil => 0
  | .cons _ _ _ rest => collectedDictionaryLength rest+1

def collectedDirectTags : CollectedPositiveTags → List (NONote × CollectedPositiveNF)
  | .nil => []
  | .cons rho A _ rest => (rho,A)::collectedDirectTags rest

/-- Unmatched coefficients are retained even when raw coefficient zero.
The valid positive source domain rules out those raw zeros. -/
def signedCollectedEntries (sign : Int) : CollectedPositiveTags → SignedCollectedRow
  | .nil => []
  | .cons rho A a rest => ((rho,A),sign*(a : Int))::signedCollectedEntries sign rest

/-- Structural-key sorted zipper, with cancellation only at equal keys. -/
def signedCollectedDifference : CollectedPositiveTags → CollectedPositiveTags → SignedCollectedRow
  | .nil, right => signedCollectedEntries (-1) right
  | left, .nil => signedCollectedEntries 1 left
  | .cons rho A a rest, .cons sigma B b tail =>
    if collectedTagKey rho A < collectedTagKey sigma B then
      ((rho,A),(a : Int))::signedCollectedDifference rest (.cons sigma B b tail)
    else if collectedTagKey rho A = collectedTagKey sigma B then
      if a=b then signedCollectedDifference rest tail
      else ((rho,A),(a : Int)-(b : Int))::signedCollectedDifference rest tail
    else ((sigma,B),-(b : Int))::signedCollectedDifference (.cons rho A a rest) tail
termination_by left right => collectedDictionaryLength left+collectedDictionaryLength right
decreasing_by
  all_goals simp_wf
  all_goals simp only [collectedDictionaryLength]
  all_goals omega

noncomputable def actualSignedCollectedValue (row : SignedCollectedRow) (x : Nat) : Int :=
  (row.map (fun entry => entry.2 * (actualProfileHead entry.1.1
    (actualCollectedPositiveEval entry.1.2 x) : Int))).sum

def SignedCollectedValid (row : SignedCollectedRow) : Prop :=
  row.Pairwise (fun a b => collectedTagKey a.1.1 a.1.2 < collectedTagKey b.1.1 b.1.2) ∧
  ∀ entry∈row, entry.2≠0 ∧ Order.IsSuccLimit entry.1.1.1.repr ∧
    entry.1.1.1.repr<epsilonZero ∧ CollectedPositiveValid entry.1.2 ∧
    collectedPositiveSupport entry.1.2=true

def signedCollectedNFRow : CollectedPositiveNF → CollectedPositiveNF → Int × Int × SignedCollectedRow
  | .mk c b tags, .mk d e rest => ((c : Int)-(d : Int),(b : Int)-(e : Int),
      signedCollectedDifference tags rest)

end LogicLineages.OrdinalComparison
