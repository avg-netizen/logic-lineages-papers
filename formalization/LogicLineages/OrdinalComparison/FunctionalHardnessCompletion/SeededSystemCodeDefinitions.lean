module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededInputCodeDefinitions
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeDefinitions
public import LogicLineages.OrdinalComparison.SourceGammaAggregateCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode
open SeededSourceCode (appCode lamCode weakenCode combineCode)

abbrev State := Nat × List (Nat × Nat)

def alignCode (a z : Nat) : Nat := appCode (lamCode 0 (weakenCode a)) z
def payloadCode (a b : Nat) : Nat :=
  appCode (combineCode b a) (appCode (combineCode a b)
    (appCode (combineCode b b) (appCode (combineCode a a) 1)))
def leftCode (a b : Nat) : Nat :=
  SourceGammaAggregateCode.eraserCode (appCode (combineCode a a) (payloadCode a b))
    (appCode (combineCode b b) (payloadCode a b))
def rightCode (a b : Nat) : Nat :=
  SourceGammaAggregateCode.eraserCode (appCode (combineCode a b) (payloadCode a b))
    (appCode (combineCode b a) (payloadCode a b))

/-- Two distinct new ground witnesses, raw indices zero and one. -/
def detectorCode (p : Nat × Nat) : Nat × Nat :=
  let q := SourcePlanPrefixCode.shiftPair 2 p
  let a := alignCode q.1 0
  let b := alignCode q.2 8
  (leftCode a b, rightCode a b)

def step (n d : Nat) (tail : State) : State :=
  let p := (SeededSourceCode.compilerCode n (SeededInputCode.subtractSeedCode n d)).1
  (tail.1 + 2, detectorCode (SourcePlanPrefixCode.shiftPair tail.1 p) ::
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

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSystemCode
