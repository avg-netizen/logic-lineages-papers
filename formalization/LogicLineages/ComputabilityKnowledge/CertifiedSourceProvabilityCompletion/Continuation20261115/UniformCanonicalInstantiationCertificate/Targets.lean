module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- The original formula is chosen AFTER the single uniform installation.
Its template-validity guard and canonical conclusion must be derived internally.
No formula-specific AST membership or native-image assumption is permitted.
The certificate count remains its numeric code, not singleton length one. -/
def CanonicalCertificate : Prop :=
 ∀ n (p : Program n) (old arithmetic : Program 1) (x : Program 3)
 (I : UniformClosedRule13Certificate.Installation p old arithmetic x),
 ∀ (f : Formula 1) ctx (raw index fuel : Term ctx),
 let template := Term.numeral (n := ctx) (FullFormulaInstantiation.templateCode f)
 let F := FullFormulaInstantiation.formulaValue I.ctag I.atag f raw
 let code := UniformClosedRule13Certificate.certificate I.ctag I.constructorTag template raw
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (Continuation20261114.RawReflexivityDispatcher.valid I.vtag raw)
   (.conj
    (.equal (LiteralCheckerAcceptance.runCall I.iteratorTag I.ptag index fuel code)
     (canonicalOutput I.ptag I.ctag I.atag f raw))
    (.conj
     (.equal (LiteralCheckerAcceptance.coreCall I.coreTag index fuel .zero (.add F F) code) (.succ .zero))
     (SixSol20261112.Fuel.success I.verifierTag index fuel .zero (.add F F) code)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformCanonicalInstantiationCertificate.Targets
