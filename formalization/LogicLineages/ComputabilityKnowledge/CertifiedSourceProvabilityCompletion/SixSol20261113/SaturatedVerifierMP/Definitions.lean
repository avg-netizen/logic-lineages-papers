module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.LiteralCoreMP.Targets
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierCore.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP
open GorbowSyntax SixSol20261112.Fuel LiteralRawMP LiteralMPRun
/-- Two original outer-verifier acceptances, at independently quantified
runtime fuels. The implication and antecedent use their original full formula
codes, not semantic formulas or substituted native syntax witnesses. -/
def inputAcceptance {ctx : Nat} (vtag atag ctag : Nat)
 (context phi psi imp ant index s t : Term ctx) : Formula ctx :=
 .conj (success vtag index s context
  (.add (implicationRaw atag ctag phi psi) (implicationRaw atag ctag phi psi)) imp)
  (success vtag index t context (.add phi phi) ant)
/-- Literal certificate MP at the internal common bound s+t. The original
canonical constructor and original requested output code are unchanged.
This is a registry-level verifier theorem, NOT source Pr_D implication
distribution, self-reference, HB2 or HB3. -/
def preservation {ctx : Nat} (vtag atag ctag mtag : Nat)
 (context phi psi imp ant index s t : Term ctx) : Formula ctx :=
 .imp (inputAcceptance vtag atag ctag context phi psi imp ant index s t)
  (success vtag index (.add s t) context (.add psi psi) (certificate mtag context psi imp ant))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP
