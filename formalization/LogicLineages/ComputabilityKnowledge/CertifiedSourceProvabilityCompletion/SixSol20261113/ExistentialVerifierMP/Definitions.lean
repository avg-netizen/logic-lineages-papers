module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedVerifierMP.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP
open GorbowSyntax SixSol20261112.Fuel LiteralRawMP
/-- Actual bounded-search verifier provability. Fuel is the outer witness,
certificate the inner witness: under both binders var1=fuel and var0=cert.
All original terms are lifted twice, preserving free variables and avoiding
capture. This is not a semantic assertion that code denotes a formula. -/
def provability {ctx : Nat} (vtag : Nat) (index context code : Term ctx) : Formula ctx :=
 .ex (.ex (success vtag (liftTerm (liftTerm index)) (.var 1)
  (liftTerm (liftTerm context)) (liftTerm (liftTerm code)) (.var 0)))
/-- Ordinary raw-code provability MP. Both input fuel/certificate pairs are
internal existentials, not externally supplied witnesses. Their sum and the
original canonical MP certificate are constructed internally in the proof
and hidden by the output existentials. Not published Pr_D or HB2/HB3. -/
def distribution {ctx : Nat} (vtag atag ctag : Nat) (index context phi psi : Term ctx) : Formula ctx :=
 .imp (provability vtag index context
  (.add (implicationRaw atag ctag phi psi) (implicationRaw atag ctag phi psi)))
  (.imp (provability vtag index context (.add phi phi))
   (provability vtag index context (.add psi psi)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.ExistentialVerifierMP
