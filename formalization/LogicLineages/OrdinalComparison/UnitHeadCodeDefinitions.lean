module
public import LogicLineages.OrdinalComparison.UnitHeadEvaluationDefinitions
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxExtractionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitHeadCode

/-- Replace exactly variable leaves by literal one; preserve remaining raw
leaf payloads and all binary tags. Malformed inputs stay explicitly totalized
by the existing ordinal fold/extraction, not by an ordinal oracle. -/
def unitLeaf (n : Nat) : Nat := if n % 8 = 3 then 1 else n
def unitBranch (tag a b : Nat) : Nat := 8 * Nat.pair a b + tag
def unitCode (n : Nat) : Nat := OrdinalSyntax.fold unitLeaf unitBranch n

def positiveCode (n : Nat) : Option Nat := (OrdinalSyntax.extraction (unitCode n)).1

def classify (n : Nat) : Option (Nat × Bool × Nat) :=
  (positiveCode n).map (fun a => (UnitHeadEvaluation.normalCode a,
    UnitHeadEvaluation.finiteCode a,UnitHeadEvaluation.finiteValueCode a))
end LogicLineages.OrdinalComparison.Source.UnitHeadCode
