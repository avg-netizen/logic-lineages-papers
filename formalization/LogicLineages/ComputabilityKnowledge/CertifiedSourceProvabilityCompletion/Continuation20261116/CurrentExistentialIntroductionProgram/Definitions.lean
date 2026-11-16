module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBCertificateQuantifierProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
abbrev neg {n : Nat} (a : Program n) := FixedFormulaSubstitution.unary 6 a
abbrev imp {n : Nat} (a b : Program n) := FixedFormulaSubstitution.binary 7 a b
abbrev allCode {n : Nat} (a : Program n) := FixedFormulaSubstitution.unary 10 a
abbrev exCode {n : Nat} (a : Program n) := FixedFormulaSubstitution.unary 11 a
def logicalSingleton {n : Nat} (isExists : Bool) (a b : Program n) : Program n :=
 .composition (OriginalQuantifierLogicalProducers.singletonConstructor isExists) (Fin.cases a (Fin.cases b Fin.elim0))
def compose {n : Nat} (P Q R hqr hpq : Program n) : Program n :=
 CurrentRecursionStepProgram.mpUnderProgram P Q R
  (CurrentRecursionStepProgram.liftProgram (imp Q R) P hqr) hpq
/-- Literal original DNE finite recipe, including fixed truth reflexivity. -/
def doubleNegation {n : Nat} (p : Program n) : Program n :=
 let R := constant n (Encodable.encode (GorbowFormulaPrefixCode.encode (.equal .zero .zero : Formula 0)))
 let A := neg (neg p)
 let hC1 := logicalSingleton false (neg R) (neg p)
 let hK := CurrentRecursionStepProgram.propositional false A (neg (neg R)) A
 let hfirst := compose A (imp (neg (neg R)) A) (imp (neg p) (neg R)) hC1 hK
 let hC2 := logicalSingleton false p R
 let hsecond := compose A (imp (neg p) (neg R)) (imp R p) hC2 hfirst
 let htruth := CurrentRecursionStepProgram.reflexivity
  (constant n (Encodable.encode (GorbowTermPrefixCode.encode (Term.zero : Term 0))))
 CurrentRecursionStepProgram.mpUnderProgram A R p hsecond
  (CurrentRecursionStepProgram.liftProgram R A htruth)
def instantiateCode {n : Nat} (a witness : Program n) : Program n :=
 applyOne HistoryCodec.predecessor (applyTwo UniformClosedInstanceRecognizer.instanceCode a witness)
/-- Original rule, not a supplied rule certificate. -/
def rule {n : Nat} (a witness : Program n) : Program n :=
 let P := allCode (neg a)
 let I := instantiateCode a witness
 let hInstantiate := CurrentRecursionBaseProgram.allInstance (neg a) witness
 let hDNE := doubleNegation P
 let hbridge := compose (neg (neg P)) P (neg I) hInstantiate hDNE
 let hC := logicalSingleton false (neg P) I
 let hneg := CurrentRecursionBaseProgram.mp (imp I (neg P)) hC hbridge
 let hex := logicalSingleton true a (constant n 0)
 compose I (neg P) (exCode a) hex hneg
/-- Runtime inputs matrix, closed witness, actual accepted-instance certificate. -/
def program : Program 3 := CurrentRecursionBaseProgram.mp (exCode (.projection 0))
 (rule (.projection 0) (.projection 1)) (.projection 2)

def logicalNumber (ax : GorbowPACore.LogicalInstance 0) : Nat :=
 GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine ax]
def composeNumber (P Q R : Formula 0) (hqr hpq : Nat) : Nat :=
 CurrentImplicationCertificate.mpUnderNumber P Q R (CurrentImplicationCertificate.liftNumber (.imp Q R) P hqr) hpq
def doubleNegationNumber (p : Formula 0) : Nat :=
 let R : Formula 0 := .equal .zero .zero
 let A := p.neg.neg
 let hC1 := logicalNumber (.classicalContraposition R.neg p.neg)
 let hK := UniformClosedPropositional.singletonNumber false A R.neg.neg A
 let hfirst := composeNumber A (.imp R.neg.neg A) (.imp p.neg R.neg) hC1 hK
 let hC2 := logicalNumber (.classicalContraposition p R)
 let hsecond := composeNumber A (.imp p.neg R.neg) (.imp R p) hC2 hfirst
 let htruth := logicalNumber (.reflexive .zero)
 CurrentImplicationCertificate.mpUnderNumber A R p hsecond (CurrentImplicationCertificate.liftNumber R A htruth)
def ruleNumber (a : Formula 1) (witness : Term 0) : Nat :=
 let P := a.neg.all
 let I := GorbowStandardInstances.instantiate a witness
 let hInstantiate := logicalNumber (.allInstantiate a.neg witness)
 let hbridge := composeNumber P.neg.neg P I.neg hInstantiate (doubleNegationNumber P)
 let hC := logicalNumber (.classicalContraposition P.neg I)
 let hneg := GorbowTheoryCertificateOperations.mpCertificate 0
  (GorbowSortedSyntaxCode.formulaCode (.imp I P.neg)) hC hbridge
 composeNumber I P.neg a.ex (logicalNumber (.existsDualBackward a)) hneg
def number (a : Formula 1) (witness : Term 0) (code : Nat) : Nat :=
 GorbowTheoryCertificateOperations.mpCertificate 0 (GorbowSortedSyntaxCode.formulaCode a.ex)
  (ruleNumber a witness) code
/-- All new syntax is fixed BEFORE verifier/source selection. The complete
previous quantifier/checker bundle is retained literally; no new-root input. -/
def extra {k : Nat} (f : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (rawOld ar : Program 1) (baseX : Program 3) : Program 6 :=
 ReflexivityInstalled.bundle
  [⟨6,CurrentQuantifierLogicalSource.extra f lhs rhs t rawOld ar baseX⟩,⟨3,program⟩]

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram
