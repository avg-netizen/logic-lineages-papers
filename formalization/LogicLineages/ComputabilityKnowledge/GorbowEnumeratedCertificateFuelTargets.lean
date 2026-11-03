module

public import LogicLineages.ComputabilityKnowledge.GorbowEnumeratedProvabilityDefinitions
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsDefinitions

@[expose] public section
/-! Exact external bridge for the actual bounded universal verifier. The same
numeric certificates survive increased fuel; the already accepted literal MP
constructor works at max fuel. No internal HB condition, source Base adequacy,
or new certificate encoding is introduced. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowEnumeratedCertificateFuel.Targets
open GorbowSyntax GorbowSortedSyntaxCode GorbowEnumeratedProvability
open GorbowTheoryCertificateOperations

/-- Arbitrary raw inputs, preserving the identical certificate number. -/
def CertificateFuelMonotonicity : Prop := ∀ (c : Code) s t, s ≤ t →
  ∀ n formula certificate, check (c,s) n formula certificate=true →
    check (c,t) n formula certificate=true

/-- The existing literal MP algorithm, arbitrary accepted certificates,
arbitrary formula contexts, one unchanged ordinary axiom program index. -/
def ModusPonensMaxFuel : Prop := ∀ (c : Code) s t n (a b : Formula n) ci ca,
  check (c,s) n (formulaCode (.imp a b)) ci=true →
  check (c,t) n (formulaCode a) ca=true →
  check (c,max s t) n (formulaCode b)
    (mpCertificate n (formulaCode b) ci ca)=true

def Target : Prop := CertificateFuelMonotonicity ∧ ModusPonensMaxFuel

end LogicLineages.ComputabilityKnowledge.GorbowEnumeratedCertificateFuel.Targets
