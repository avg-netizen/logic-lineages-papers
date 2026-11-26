module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowNamedNumeralCertificatesProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open HistoryRuleSuffix CurrentRecursionBaseProgram
/-- The original two-variable alias body. No additional tag binder. -/
def matrix : Formula 2 :=
 .equal (.universalFunction (GorbowNamedDefiningTheory.headerVariables (2,0)))
  (call GorbowSourceRegistryPadding.functionTag (GorbowNamedDefiningTheory.headerVariables (2,0) ::ᵥ nil))
def raw (i : Fin 2) : Program 2 := applyOne LiteralNumeralPrefix.numeralCode (.projection i)
/-- Literal original rule4 singleton for the actual closed named alias. -/
def seedProgram : Program 2 :=
 axiomProgram (constant 2 (Encodable.encode (GorbowFormulaPrefixCode.encode (GorbowNamedDefiningTheory.functionAlias (2,0)))))
/-- Specialize the tail variable s first, leaving r protected. -/
def tailProgram : Program 2 :=
 mp (quote (.all matrix) (fun _ => raw 1))
  (allInstance (headQuote (.all matrix) Fin.elim0) (raw 1)) seedProgram
/-- Then specialize r. Both MP operations and both all13 singletons are literal. -/
def program : Program 2 :=
 mp (quote matrix raw) (allInstance (headQuote matrix (fun _ => raw 1)) (raw 0)) tailProgram
/-- Independent original specialization recipe, not evaluation of program. -/
def number (r s : Nat) : Nat :=
 PrescribedRuntimeSpecialization.produce matrix
  (Fin.cases (Term.numeral r) (Fin.cases (Term.numeral s) Fin.elim0))
  (PrescribedSourceAxiomSpecialization.seed matrix)
/-- Exact literal target equation; no numerical replacement for binaryCodeTerm. -/
def aliasFormula (r s : Nat) : Sentence :=
 .equal (GorbowBooleanTruth.binaryCodeTerm 0 (Term.numeral r) (Term.numeral s))
  (call GorbowSourceRegistryPadding.functionTag
   (GorbowRegistryTuple.headerTerm 2 0 [Term.numeral r,Term.numeral s] ::ᵥ nil))
/-- Raw code of that same equation on arbitrary symbolic numeral arguments. -/
def headerCode {ctx : Nat} (J : PrescribedRuntimeCallCongruence.Tags) (r s : Term ctx) : Term ctx :=
 PrescribedRuntimeCallCongruence.headerValue J .zero
  (LiteralNumeralPrefix.numeralCall J.numeralTag r ::ᵥ LiteralNumeralPrefix.numeralCall J.numeralTag s ::ᵥ nil)
def aliasCode {ctx : Nat} (J : PrescribedRuntimeCallCongruence.Tags) (r s : Term ctx) : Term ctx :=
 PrescribedRuntimeEquality.equalValue J.ctag J.atag
  (FixedFormulaSubstitution.unaryValue J.ctag 5 (headerCode J r s))
  (PrescribedRuntimeCallCongruence.callValue J (Term.numeral GorbowSourceRegistryPadding.functionTag)
   (headerCode J r s ::ᵥ nil))
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle [⟨6,CurrentPublishedProvabilityIntroduction.extra f lhs rhs t rawOld ar baseX⟩,⟨2,program⟩]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNamedAliasCertificate
