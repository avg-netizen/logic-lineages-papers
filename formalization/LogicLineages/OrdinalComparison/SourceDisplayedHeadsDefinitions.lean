module
public import LogicLineages.OrdinalComparison.PositiveSourceDomainDefinitions
public import LogicLineages.OrdinalComparison.CollectedNormalizeDefinitions
public import LogicLineages.OrdinalComparison.SignedCollectedDifferenceDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal original h-node occurrence count; sharing is expanded as source
syntax. No equality with a normalized representation's size is assumed. -/
def comparisonPositiveSourceHeadCount : FixedLimitPositiveExpr → Nat
  | .constant _ | .input => 0
  | .add E F => comparisonPositiveSourceHeadCount E+comparisonPositiveSourceHeadCount F
  | .head _ E => comparisonPositiveSourceHeadCount E+1

/-- Displayed top-level open source heads. We do NOT recurse under a head
when forming this forest: its raw argument is retained as one owned subtree. -/
def comparisonDisplayedSourceHeads : FixedLimitPositiveExpr → List (NONote × FixedLimitPositiveExpr)
  | .constant _ | .input => []
  | .add E F => comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F
  | .head rho E => if positiveExprHasInput E then [(rho,E)] else []

def collectedSourceRootTags : CollectedPositiveNF → List (NONote × CollectedPositiveNF)
  | .mk _ _ tags => collectedDirectTags tags

def encodedDisplayedSourceHeadsStep (n : Nat) (table : List (List (Nat × Nat))) : List (Nat × Nat) :=
  if n%4=0 ∨ n%4=1 then [] else let p := (n/4).unpair
    if n%4=2 then table.getD p.1 []++table.getD p.2 []
    else if (encodedPositiveSourceData p.2).2=1 then [(p.1,p.2)] else []

def encodedDisplayedSourceHeadsTable : Nat → List (List (Nat × Nat))
  | 0 => []
  | n+1 => encodedDisplayedSourceHeadsTable n++
      [encodedDisplayedSourceHeadsStep n (encodedDisplayedSourceHeadsTable n)]

def encodedDisplayedSourceHeads (n : Nat) : List (Nat × Nat) :=
  (encodedDisplayedSourceHeadsTable (n+1)).getD n []

end LogicLineages.OrdinalComparison
