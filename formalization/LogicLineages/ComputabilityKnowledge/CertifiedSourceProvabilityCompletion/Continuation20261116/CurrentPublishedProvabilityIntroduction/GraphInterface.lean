module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.Preflight
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.GraphOperations
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInterface
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
abbrev Tags := CurrentExistentialIntroductionProgram.GraphInterface.Tags
abbrev Installation {n : Nat} (p : Program n) (J : Tags) := CurrentExistentialIntroductionProgram.GraphInterface.Installation p J
abbrev numeral {ctx : Nat} (ntag : Nat) (a : Term ctx) := LiteralNumeralPrefix.numeralCall ntag a
def innerInputs {ctx : Nat} (ntag : Nat) (v : List.Vector (Term ctx) 7) : List.Vector (Term ctx) 4 :=
 numeral ntag (v.get 2) ::ᵥ numeral ntag (v.get 1) ::ᵥ v.get 4 ::ᵥ numeral ntag (v.get 0) ::ᵥ nil
def outerInputs {ctx : Nat} (ntag : Nat) (v : List.Vector (Term ctx) 7) : List.Vector (Term ctx) 3 :=
 numeral ntag (v.get 1) ::ᵥ v.get 4 ::ᵥ numeral ntag (v.get 0) ::ᵥ nil
def innerValue {ctx : Nat} (J : Tags) (ntag : Nat) (v : List.Vector (Term ctx) 7) : Term ctx :=
 FixedFormulaSubstitution.formulaValue J.ctag J.atag (innerInputs ntag v) bodyTemplate innerEnvironment
def outerValue {ctx : Nat} (J : Tags) (ntag : Nat) (v : List.Vector (Term ctx) 7) : Term ctx :=
 FixedFormulaSubstitution.formulaValue J.ctag J.atag (outerInputs ntag v) (.ex bodyTemplate) outerEnvironment
def introValue {ctx : Nat} (etag : Nat) (matrix witness code : Term ctx) : Term ctx :=
 call etag (matrix ::ᵥ witness ::ᵥ code ::ᵥ nil)
def value {ctx : Nat} (J : Tags) (ntag etag : Nat) (v : List.Vector (Term ctx) 7) : Term ctx :=
 let first := introValue etag (innerValue J ntag v) (numeral ntag (v.get 3)) (v.get 6)
 let second := introValue etag (outerValue J ntag v) (numeral ntag (v.get 2)) first
 CurrentExistentialIntroductionProgram.GraphInterface.liftValue J
  (FixedFormulaSubstitution.unaryValue J.ctag 11 (outerValue J ntag v)) (v.get 5) second
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.GraphInterface
