module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededSystemCodeDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.HardnessDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode
open OriginalDomain

def sourcePair (strict : Bool) {n : Nat} (s : System n) :
    OriginalTerm (SeededSystem.compile s).context .ground ×
      OriginalTerm (SeededSystem.compile s).context .ground :=
  if strict then ((SeededSystem.strictPair s).2, (SeededSystem.strictPair s).1)
  else SeededSystem.weakPair s

def validRow (n : Nat) (row : List MonomialCode) : Bool :=
  row.foldr (fun m b => SeededInputCode.validMonomial n m && b) true
def validSystem (c : SystemCode) : Bool :=
  c.2.foldr (fun row b => validRow c.1 row && b) true

def queryCode (strict : Bool) (n : Nat) (rows : List Nat) : Nat :=
  let p := if strict then
    ((SeededSystemCode.strictCode n rows).2, (SeededSystemCode.strictCode n rows).1)
    else SeededSystemCode.weakCode n rows
  Encodable.encode (SeededSystemCode.contextCode n rows, p.1, p.2)

/-- A literal unsatisfiable one-equation input. It supplies a bounded source
query which is universally true, for either strictness convention. -/
def fallbackSystem : System 0 := [.unit]
def fallbackCode (strict : Bool) : Nat := queryCode strict 0 [0]

/-- A total map on EVERY natural input code, including undecodable data and
out-of-range unknown references. The latter do not enter the valid branch. -/
def reduceCode (strict : Bool) (e : Nat) : Nat :=
  match Encodable.decode (α := SystemCode) e with
  | none => fallbackCode strict
  | some c => if validSystem c then queryCode strict c.1 (SeededInputCode.inputCode c)
    else fallbackCode strict

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededQueryCode
