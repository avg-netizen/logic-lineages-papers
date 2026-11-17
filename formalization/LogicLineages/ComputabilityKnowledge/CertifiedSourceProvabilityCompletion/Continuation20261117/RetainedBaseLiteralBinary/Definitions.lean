module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseSourceCalculation.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedHeaderTransport.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



/-- Literal original binaryCodeTerm syntax evaluated as syntax on numeral-coded
symbolic inputs; not an alternative named function or a numerical oracle. -/
def rawBinary {ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags) (r s : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.termValue K.ctag K.atag (PrescribedRuntimeSpecialization.runtimeEnvironment 2)
  (LiteralNumeralPrefix.numeralCall K.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall K.numeralTag s ::ᵥ nil)
  (GorbowBooleanTruth.binaryCodeTerm 0 (.var 0) (.var 1))

/-- Explicit specialization of actual original named alias. No absent alias
producer occurrence is assumed. Its two seed constructors use rule13Tag. -/
def aliasCertificate {ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags) (rule13Tag : Nat)
 (r s : Term ctx) : Term ctx :=
 PrescribedSourceAxiomSpecialization.certificate K.mtag K.ctag K.atag rule13Tag
  CurrentNamedAliasCertificate.matrix
  (LiteralNumeralPrefix.numeralCall K.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall K.numeralTag s ::ᵥ nil)

def certificate {ctx : Nat} (K : PrescribedRuntimeCallCongruence.Tags) (rule13Tag headerProducerTag : Nat)
 (pF0 : Program 1) (pCK : Program 2) (box : Program 6) (outer : Program 5)
 (peelTag baseProducerTag : Nat) (r s : Term ctx) : Term ctx :=
 let h := CurrentNamedAliasCertificate.headerCode K r s
 let v := GorbowRegistryTuple.headerTerm 2 0 [r,s]
 let nv := LiteralNumeralPrefix.numeralCall K.numeralTag v
 let left := FixedFormulaSubstitution.unaryValue K.ctag 5 h
 let middle := callValue K (Term.numeral 6) (h ::ᵥ nil)
 let right := callValue K (Term.numeral 6) (nv ::ᵥ nil)
 let headerStep := PrescribedRuntimeCallCongruence.unaryCertificate K CurrentNamedHeaderTransport.unary h nv
  (call headerProducerTag (r ::ᵥ s ::ᵥ nil))
 let beforeEvaluation := transitivityCertificate K.mtag K.ctag K.atag K.constructorTag
  left middle right (aliasCertificate K rule13Tag r s) headerStep
 transitivityCertificate K.mtag K.ctag K.atag K.constructorTag left right
  (LiteralNumeralPrefix.numeralCall K.numeralTag (call 6 (v ::ᵥ nil)))
  beforeEvaluation (RetainedBaseSourceCalculation.certificate K pF0 pCK box outer peelTag baseProducerTag v)

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseLiteralBinary
