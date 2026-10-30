module

public import LogicLineages.ComputabilityKnowledge.GorbowRegistryDecoder
public import LogicLineages.ComputabilityKnowledge.GorbowNumericCertificate
public import LogicLineages.ComputabilityKnowledge.GorbowRevisionSemantics

@[expose] public section

/-! Concrete executable Boolean fragment of the source U/u syntax registry.
U and u are separate symbol namespaces. U header(1,0,[c]) is sentencehood;
u header(1,0,[c]) is negation; u header(2,t,[a,b]), t=0,1,2, gives implication,
conjunction, disjunction. Other headers have literal false/zero defaults.
The source formula encoding remains the accepted formulaNumber, not header.
No Base defining axiom, representability or DCB claim is made here. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistry
open GorbowSyntax GorbowCodeConstructors GorbowRegistryTuple GorbowRegistryDecoder GorbowNumericCertificate

def unaryNumber (tag code : Nat) : Nat :=
  ((decodeFormula code).map (fun raw => number (unary tag raw))).getD 0

def binaryNumber (tag a b : Nat) : Nat :=
  (do let ra ← decodeFormula a
      let rb ← decodeFormula b
      pure (number (binary tag ra rb))).getD 0

def sentenceCode (code : Nat) : Bool :=
  match decodeFormula code with
  | some raw => GorbowSyntaxValidation.validFormula 0 raw
  | none => false

def relationProgram (code : Nat) : Bool :=
  match decodeHeader code with
  | some (arity,tag,args) => decide (arity=1 ∧ tag=0 ∧ args.length=1) && sentenceCode (args.getD 0 0)
  | none => false

def functionProgram (code : Nat) : Nat :=
  match decodeHeader code with
  | some (arity,tag,args) =>
    if arity=1 ∧ tag=0 ∧ args.length=1 then unaryNumber 6 (args.getD 0 0)
    else if arity=2 ∧ tag<3 ∧ args.length=2 then binaryNumber (tag+7) (args.getD 0 0) (args.getD 1 0)
    else 0
  | none => 0

def ground : GorbowRevisionSemantics.Ground where
  universalRelation := fun code => relationProgram code=true
  universalFunction := functionProgram
end LogicLineages.ComputabilityKnowledge.GorbowBooleanRegistry
