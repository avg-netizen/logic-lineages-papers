module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode
open SeededSourceCode (appCode lamCode)
abbrev State := Nat × List (Nat × Nat)

/-- Unlike the seeded compiler, no seed subtraction is performed. The exact
compiler calibration below proves the seed branch is unreachable on every
actual plain typed expression. Raw malformed rows still have total defaults. -/
def step (n d : Nat) (tail : State) : State :=
  let p := (SeededSourceCode.compilerCode n d).1
  (tail.1 + 2, SeededSystemCode.detectorCode (SourcePlanPrefixCode.shiftPair tail.1 p) ::
    SourcePlanPrefixCode.shiftPairs 2 tail.2)
def systemCode (n : Nat) (rows : List Nat) : State := rows.foldr (step n) (0, [])
def strictCode (n : Nat) (rows : List Nat) : Nat × Nat :=
  SourceGammaAggregateCode.aggregateCode (systemCode n rows).2
def weakCode (n : Nat) (rows : List Nat) : Nat × Nat :=
  let p := strictCode n rows
  (appCode (lamCode 0 1) p.2, appCode (lamCode 0 0) p.1)
def contextCode (n : Nat) (rows : List Nat) : List Nat :=
  List.replicate (systemCode n rows).1 0 ++
    List.replicate n (SyntaxCode.typeCode FunctionalDetector.unary)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.PlainSystemCode
