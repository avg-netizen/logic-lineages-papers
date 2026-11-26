module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralRecursionProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeCallCongruence PrescribedRuntimeEquality

/-- Literal first defining equation of the original recursion node. -/
def rootFormula (m tag : Nat) : Formula m :=
 .equal (call tag (.zero ::ᵥ argumentVariables m)) (call (tag+1) (argumentVariables m))
abbrev numeralValues := @CurrentCompositionCertificate.numeralValues
/-- Original recursionBase recipe: specialize the root zero equation, then
one original transitivity with the supplied base-child certificate. -/
def number {m : Nat} (tag : Nat) (inputs : List.Vector Nat m) (result childCode : Nat) : Nat :=
 let av := GorbowPRNumeralCalculation.numeralArguments inputs
 let seed := PrescribedRuntimeSpecialization.produce (rootFormula m tag)
  (fun i => Term.numeral (inputs.get i)) (PrescribedSourceAxiomSpecialization.seed (rootFormula m tag))
 transitivityNumber (call tag (.zero ::ᵥ av)) (call (tag+1) av) (Term.numeral result) seed childCode
def certificate {arity k m ctx : Nat} {p : Program arity} {installed : Formula 1}
 {lhs rhs : Term 1} {t : Term k} {old a : Program 1} {x : Program 3}
 (I : CumulativeUniformRule12Registry.JointInstallation p installed lhs rhs t old a x)
 (tag : Nat) (inputs : List.Vector (Term ctx) m) (result childCode : Term ctx) : Term ctx :=
 let J := tags I
 let av := numeralValues J.numeralTag inputs
 let zero := LiteralNumeralPrefix.numeralCall J.numeralTag (.zero : Term ctx)
 let parent := callValue J (Term.numeral tag) (zero ::ᵥ av)
 let child := callValue J (Term.numeral (tag+1)) av
 let output := LiteralNumeralPrefix.numeralCall J.numeralTag result
 let seed := PrescribedSourceAxiomSpecialization.certificate J.mtag I.previous.current.ctag
  I.previous.current.atag I.previous.current.constructorTag (rootFormula m tag) av
 transitivityCertificate J.mtag J.ctag J.atag J.constructorTag parent child output seed childCode
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseCertificate
