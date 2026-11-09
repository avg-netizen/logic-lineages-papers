module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.EffectiveNumeralFamilyProof
public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedCertificateFuelProof

@[expose] public section
/-! Numeric MP for the actual published conditional-proof predicate. The
rho wrapper is retained in all three literal sorted formula codes. This
external constructor is not an internal HB2 theorem. -/
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBCertificateMP
open GorbowSyntax GorbowTheoryProof GorbowSortedSyntaxCode GorbowTheoryCertificateOperations

/-- Original singleton logical S-scheme certificate. -/
def sCertificate (rho sigma tau : Sentence) : Nat :=
  GorbowNumericCertificate.certificateNumber [GorbowProofChecker.logicalLine (.s rho sigma tau)]

def conditionalMP (rho sigma tau : Sentence) (ci ca : Nat) : Nat :=
  mpCertificate 0 (formulaCode (.imp rho tau))
    (mpCertificate 0 (formulaCode (.imp (.imp rho sigma) (.imp rho tau)))
      (sCertificate rho sigma tau) ci) ca

theorem conditionalMPPrimitive (rho sigma tau : Sentence) :
    Primrec (fun z : Nat × Nat => conditionalMP rho sigma tau z.1 z.2) := by
  have hmid : Primrec (fun z : Nat × Nat => mpCertificate 0
      (formulaCode (.imp (.imp rho sigma) (.imp rho tau))) (sCertificate rho sigma tau) z.1) :=
    GorbowTheoryCertificateOperationsProof.effectiveModusPonens.comp
      ((Primrec.const 0).pair ((Primrec.const _).pair
        ((Primrec.const _).pair Primrec.fst)))
  exact GorbowTheoryCertificateOperationsProof.effectiveModusPonens.comp
    ((Primrec.const 0).pair ((Primrec.const _).pair (hmid.pair Primrec.snd)))

theorem conditionalMPMaxFuel (rho sigma tau : Sentence) (c : Nat.Partrec.Code)
    (s t ci ca : Nat)
    (hi : GorbowEnumeratedProvability.check (c,s) 0 (formulaCode (.imp rho (.imp sigma tau))) ci = true)
    (ha : GorbowEnumeratedProvability.check (c,t) 0 (formulaCode (.imp rho sigma)) ca = true) :
    GorbowEnumeratedProvability.check (c,max s t) 0 (formulaCode (.imp rho tau))
      (conditionalMP rho sigma tau ci ca) = true := by
  let ax := GorbowEnumeratedProvability.axiomCheck (c,max s t)
  have hi' := GorbowEnumeratedCertificateFuel.Proof.certificateFuelMonotonicity c s (max s t)
    (le_max_left s t) 0 (formulaCode (.imp rho (.imp sigma tau))) ci hi
  have ha' := GorbowEnumeratedCertificateFuel.Proof.certificateFuelMonotonicity c t (max s t)
    (le_max_right s t) 0 (formulaCode (.imp rho sigma)) ca ha
  have hs : GorbowTheoryNumericCertificate.check ax 0
      (formulaCode (.imp (.imp rho (.imp sigma tau)) (.imp (.imp rho sigma) (.imp rho tau))))
      (sCertificate rho sigma tau) = true :=
    EffectiveNumeral.Family.compiledCertificate ax (.logical (.s rho sigma tau))
  have hmid := GorbowTheoryCertificateOperationsProof.numericModusPonens ax 0
    (.imp rho (.imp sigma tau)) (.imp (.imp rho sigma) (.imp rho tau))
    (sCertificate rho sigma tau) ci hs hi'
  exact GorbowTheoryCertificateOperationsProof.numericModusPonens ax 0
    (.imp rho sigma) (.imp rho tau)
    (mpCertificate 0 (formulaCode (.imp (.imp rho sigma) (.imp rho tau)))
      (sCertificate rho sigma tau) ci) ca hmid ha'

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.HBCertificateMP
