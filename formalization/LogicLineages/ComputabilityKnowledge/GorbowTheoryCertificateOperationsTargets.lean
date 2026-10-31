module
public import LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsTargets
open GorbowSyntax GorbowTheoryCertificateOperations GorbowSortedSyntaxCode

def SuccessfulHistoryExtension : Prop :=
  ∀ (axCheck : List Nat → Bool) (history : GorbowProofChecker.History)
    (lines : List GorbowProofChecker.Line) (out tail : GorbowProofChecker.History),
    GorbowTheoryChecker.run axCheck history lines = some out →
      GorbowTheoryChecker.run axCheck (history ++ tail) lines = some (out ++ tail)

def NumericModusPonens : Prop :=
  ∀ (axCheck : List Nat → Bool) (n : Nat) (a b : Formula n) (ci ca : Nat),
    GorbowTheoryNumericCertificate.check axCheck n (formulaCode (.imp a b)) ci = true →
    GorbowTheoryNumericCertificate.check axCheck n (formulaCode a) ca = true →
    GorbowTheoryNumericCertificate.check axCheck n (formulaCode b)
      (mpCertificate n (formulaCode b) ci ca) = true

def NumericGeneralization : Prop :=
  ∀ (axCheck : List Nat → Bool) (n : Nat) (a : Formula (n+1)) (c : Nat),
    GorbowTheoryNumericCertificate.check axCheck (n+1) (formulaCode a) c = true →
    GorbowTheoryNumericCertificate.check axCheck n (formulaCode (.all a))
      (generalizeCertificate n (formulaCode (.all a)) c) = true

def EffectiveModusPonens : Prop :=
  Primrec (fun z : Nat × Nat × Nat × Nat => mpCertificate z.1 z.2.1 z.2.2.1 z.2.2.2)

def EffectiveGeneralization : Prop :=
  Primrec (fun z : Nat × Nat × Nat => generalizeCertificate z.1 z.2.1 z.2.2)

end LogicLineages.ComputabilityKnowledge.GorbowTheoryCertificateOperationsTargets
