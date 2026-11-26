module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeUniformRule12Source.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralEqualityProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Literal original logical singleton; not an identification with any opaque
HasCertificates choice. -/
def replacementNumber (matrix : Formula 1) (left right : Term 0) : Nat :=
 GorbowNumericCertificate.certificateNumber
  [GorbowProofChecker.logicalLine (.equalityReplace matrix left right)]
def transitivityNumber (t u v : Term 0) (htu huv : Nat) : Nat :=
 GorbowTheoryCertificateOperations.mpCertificate 0
  (GorbowSortedSyntaxCode.formulaCode (.equal t v))
  (GorbowTheoryCertificateOperations.mpCertificate 0
   (GorbowSortedSyntaxCode.formulaCode (.imp (.equal t u) (.equal t v)))
   (replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 t) (.var 0)) u v) huv) htu
def unaryNumber (f : Term 1) (t u : Term 0) (htu : Nat) : Nat :=
 let ft := GorbowClosedEquality.instantiateTerm f t
 let fu := GorbowClosedEquality.instantiateTerm f u
 GorbowTheoryCertificateOperations.mpCertificate 0
  (GorbowSortedSyntaxCode.formulaCode (.equal ft fu))
  (GorbowTheoryCertificateOperations.mpCertificate 0
   (GorbowSortedSyntaxCode.formulaCode (.imp (.equal ft ft) (.equal ft fu)))
   (replacementNumber (.equal (GorbowClosedEquality.liftClosedTerm 1 ft) f) t u) htu)
  (GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.reflexive ft)])
def equalValue {ctx : Nat} (ctag atag : Nat) (left right : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.binaryValue ctag atag 0 left right
def impValue {ctx : Nat} (ctag atag : Nat) (left right : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.binaryValue ctag atag 7 left right
/-- Same ordered two MP calls as the original transitivity proof. -/
def transitivityCertificate {ctx : Nat} (mtag ctag atag constructorTag : Nat)
 (t u v htu huv : Term ctx) : Term ctx :=
 let matrix := equalValue ctag atag t
  (Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (.var (0 : Fin 1)))))
 LiteralMPRun.certificate mtag .zero (equalValue ctag atag t v)
  (LiteralMPRun.certificate mtag .zero
   (impValue ctag atag (equalValue ctag atag t u) (equalValue ctag atag t v))
   (UniformClosedRule12Certificate.certificate ctag constructorTag matrix u v) huv) htu
/-- Captures arbitrary closed runtime coordinates in the original open term;
only its sole protected variable is specialized, never reinterpreted as fixed syntax. -/
def specializedValue {n inputs ctx : Nat} (ctag atag : Nat)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 (raw : List.Vector (Term ctx) inputs) (replacement : Term ctx) : Term ctx :=
 FixedFormulaSubstitution.termValue ctag atag
  (UniformRuntimeEnvironmentAgreement.specialize e) (replacement ::ᵥ raw) f
def unaryCertificate {n inputs ctx : Nat} (mtag ctag atag constructorTag rctag reflexivityTag : Nat)
 (e : FixedFormulaSubstitution.Environment n 1 inputs) (f : Term n)
 (raw : List.Vector (Term ctx) inputs) (t u htu : Term ctx) : Term ctx :=
 let ft := specializedValue ctag atag e f raw t
 let fu := specializedValue ctag atag e f raw u
 let matrix := equalValue ctag atag ft (FixedFormulaSubstitution.termValue ctag atag e raw f)
 LiteralMPRun.certificate mtag .zero (equalValue ctag atag ft fu)
  (LiteralMPRun.certificate mtag .zero
   (impValue ctag atag (equalValue ctag atag ft ft) (equalValue ctag atag ft fu))
   (UniformClosedRule12Certificate.certificate ctag constructorTag matrix t u) htu)
  (RawCumulativeLogical.certificate rctag reflexivityTag ft)
def boundEnvironment : FixedFormulaSubstitution.Environment 1 1 0 := fun i => .inl i
def rawNumeral {ctx : Nat} (t : Term 0) : Term ctx :=
 Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode t))
def core {ctx : Nat} (tag : Nat) (index fuel formula code : Term ctx) : Formula ctx :=
 .equal (LiteralCheckerAcceptance.coreCall tag index fuel .zero (.add formula formula) code) (.succ .zero)
def accepted {ctx : Nat} (coreTag verifierTag : Nat) (index fuel formula code : Term ctx) : Formula ctx :=
 .conj (core coreTag index fuel formula code)
  (SixSol20261112.Fuel.success verifierTag index fuel .zero (.add formula formula) code)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeEquality
