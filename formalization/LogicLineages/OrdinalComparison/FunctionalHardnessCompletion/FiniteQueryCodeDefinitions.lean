module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.MaskRestrictionCodeDefinitions
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededQueryCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode
open OriginalDomain

def sourcePair (strict : Bool) {n : Nat} (s : System n) :
    OriginalTerm (compileSystem s).context .ground × OriginalTerm (compileSystem s).context .ground :=
  if strict then ((strictSystemPair s).2, (strictSystemPair s).1) else weakSystemPair s

def groundQuery (strict : Bool) {n : Nat} (s : System n) : GroundQuery :=
  ⟨(compileSystem s).context, sourcePair strict s⟩
def queries (strict : Bool) {n : Nat} (s : System n) : List GroundQuery :=
  (masks n).map (fun z => groundQuery strict (restrictSystem z s))

def queryCode (strict : Bool) (n : Nat) (rows : List Nat) : Nat :=
  let p := if strict then
    ((PlainSystemCode.strictCode n rows).2, (PlainSystemCode.strictCode n rows).1)
    else PlainSystemCode.weakCode n rows
  Encodable.encode (PlainSystemCode.contextCode n rows, p.1, p.2)
def queriesCode (strict : Bool) (n : Nat) (rows : List Nat) : List Nat :=
  (MaskRestrictionCode.masksCode n).map
    (fun z => queryCode strict n (MaskRestrictionCode.restrictRows z rows))

def fallbackSystem : System 0 := [.unit]
def fallbackCode (strict : Bool) : List Nat := queriesCode strict 0 [0]

/-- Every malformed input produces the finite query list of an actual
unsatisfiable plain system. All valid inputs retain every original zero mask. -/
def reduceCode (strict : Bool) (e : Nat) : List Nat :=
  match Encodable.decode (α := SystemCode) e with
  | none => fallbackCode strict
  | some c => if SeededQueryCode.validSystem c then
      queriesCode strict c.1 (SeededInputCode.inputCode c)
    else fallbackCode strict

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.FiniteQueryCode
