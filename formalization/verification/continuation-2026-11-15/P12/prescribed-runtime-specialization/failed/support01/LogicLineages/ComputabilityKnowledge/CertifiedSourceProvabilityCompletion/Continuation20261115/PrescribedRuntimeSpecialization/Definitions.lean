module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformRuntimeSpecializationStep.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralSpecializationProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization
open GorbowSyntax GorbowFormulaSubstitution SixSol20261113
/-- The original existential proof's displayed constructor recipe, now prescribed
explicitly. This is NOT an asserted equality with an unspecified chosen witness.
Tail specialization precedes the original logical singleton and numeric MP. -/
def produce : {n : Nat} → Formula n → (Fin n → Term 0) → Nat → Nat
 | 0, _, _, antecedent => antecedent
 | n+1, f, sigma, antecedent =>
  let B := substituteFormula (liftSubstitute (fun i => sigma i.succ)) f
  GorbowTheoryCertificateOperations.mpCertificate 0
   (GorbowSortedSyntaxCode.formulaCode (substituteFormula sigma f))
   (GorbowNumericCertificate.certificateNumber
    [GorbowProofChecker.logicalLine (.allInstantiate B (sigma 0))])
   (produce (.all f) (fun i => sigma i.succ) antecedent)
def runtimeEnvironment (n : Nat) : FixedFormulaSubstitution.Environment n 0 n :=
 fun i => .inr i
def headEnvironment (n : Nat) : FixedFormulaSubstitution.Environment (n+1) 1 n :=
 Fin.cases (.inl 0) (fun i => .inr i)
def value {n ctx : Nat} (ctag atag : Nat) (f : Formula n)
 (raw : List.Vector (Term ctx) n) : Term ctx :=
 FixedFormulaSubstitution.formulaValue ctag atag raw f (runtimeEnvironment n)
/-- Same ordered constructor recursion expressed using the already installed
runtime calls. The exact numeral trace identity is a separate required theorem. -/
def certificate {ctx : Nat} (mtag ctag atag constructorTag : Nat) :
 {n : Nat} → Formula n → List.Vector (Term ctx) n → Term ctx → Term ctx
 | 0, _, _, antecedent => antecedent
 | n+1, f, raw, antecedent =>
  UniformRuntimeSpecializationStep.certificate mtag ctag atag constructorTag
   (headEnvironment n) f raw.tail raw.head
   (certificate mtag ctag atag constructorTag (.all f) raw.tail antecedent)
def numeralInputs {n ctx : Nat} (sigma : Fin n → Term 0) : List.Vector (Term ctx) n :=
 List.Vector.ofFn (fun i => Term.numeral (Encodable.encode (GorbowTermPrefixCode.encode (sigma i))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.PrescribedRuntimeSpecialization
