module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax
open ForwardTranslation

/-- Preserve refusal: both operands must be present. -/
def combineCodes (tag : Nat) (a b : Option Nat) : Option Nat := do
  let x ← a
  let y ← b
  pure (4 * Nat.pair x y + tag)

def extractionLeaf (n : Nat) : Option Nat × Option Nat :=
  if n=1 then (some 0, some 4)
  else if n=2 then (some 1, none)
  else if n%8=3 then (none, some (4*(n/8).unpair.1+1))
  else (none, none)

def extractionBranch (tag : Nat) (a b : Option Nat × Option Nat) : Option Nat × Option Nat :=
  if tag=4 then (combineCodes 2 a.1 b.1, combineCodes 2 a.2 b.2)
  else if tag=5 then (combineCodes 3 a.1 b.1, none)
  else if tag=6 then (none, combineCodes 3 a.1 b.2)
  else (none, none)

/-- Two simultaneous genuinely refusing syntax compilers. Closed-positive
heads remain literal AST codes; source variable positions remain shared. -/
def extraction (n : Nat) : Option Nat × Option Nat := fold extractionLeaf extractionBranch n
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
