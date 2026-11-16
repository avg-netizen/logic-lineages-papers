module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralImplicationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality

/-- Original HasCertificates.lift: singleton K followed by exactly one MP.
The unused K coordinate is fixed at formula A, never a new premise. -/
def liftNumber (A B : Formula 0) (code : Nat) : Nat :=
 GorbowTheoryCertificateOperations.mpCertificate 0 (GorbowSortedSyntaxCode.formulaCode (.imp B A))
  (UniformClosedPropositional.singletonNumber false A B A) code
/-- Original HasCertificates.mpUnder: singleton S, then hi, then ha.
Arbitrary numeric codes preserve the original decode/default behavior. -/
def mpUnderNumber (P Q R : Formula 0) (hi ha : Nat) : Nat :=
 GorbowTheoryCertificateOperations.mpCertificate 0 (GorbowSortedSyntaxCode.formulaCode (.imp P R))
  (GorbowTheoryCertificateOperations.mpCertificate 0
   (GorbowSortedSyntaxCode.formulaCode (.imp (.imp P Q) (.imp P R)))
   (UniformClosedPropositional.singletonNumber true P Q R) hi) ha
/-- Runtime constructor uses the actual current K singleton but the preserved
MP/formula-code programs. No tag equalities or source tuple casts are assumed. -/
def liftCertificate {arity k ctx : Nat} {p : Program arity} {f : Formula 1} {lhs rhs : Term 1}
 {t : Term k} {old a : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (A B code : Term ctx) : Term ctx :=
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag B A)
  (UniformClosedPropositionalCertificate.certificate I.currentK.ctag I.currentK.constructorTag A B A) code
/-- Runtime constructor follows the original two-MP S recipe literally. -/
def mpUnderCertificate {arity k ctx : Nat} {p : Program arity} {f : Formula 1} {lhs rhs : Term 1}
 {t : Term k} {old a : Program 1} {x : Program 3}
 (I : CumulativePropositionalSource.JointInstallation p f lhs rhs t old a x)
 (P Q R hi ha : Term ctx) : Term ctx :=
 let J := PrescribedRuntimeCallCongruence.tags I.previous
 LiteralMPRun.certificate J.mtag .zero (impValue J.ctag J.atag P R)
  (LiteralMPRun.certificate J.mtag .zero
   (impValue J.ctag J.atag (impValue J.ctag J.atag P Q) (impValue J.ctag J.atag P R))
   (UniformClosedPropositionalCertificate.certificate I.currentS.ctag I.currentS.constructorTag P Q R) hi) ha
def formulaNumeral {ctx : Nat} (f : Formula 0) : Term ctx :=
 Term.numeral (Encodable.encode (GorbowFormulaPrefixCode.encode f))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentImplicationCertificate
