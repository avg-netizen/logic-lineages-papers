module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof SixSol20261113
/-- Real two-MP certificate composition at ONE actual CORE/checker and common
runtime index/fuel. Only the input equality certificate is assumed accepted,
inside the object implication. Replacement and successor reflexivity are
constructed and verified, not supplied as assumptions. Output is the exact
nested canonical MP certificate, with original encoded iteration bounds. -/
def InternalCoreCongruence : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (RawSuccCongruence.inputRaw I.ctag I.atag t u) (RawSuccCongruence.inputRaw I.ctag I.atag t u)) cert) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
       (.add (RawSuccCongruence.outputRaw I.ctag I.atag t u) (RawSuccCongruence.outputRaw I.ctag I.atag t u))
       (RawSuccCongruence.certificate I.mpTag I.replaceTag I.reflexivityTag I.ctag I.atag t u cert)) (.succ .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRetainedSuccCongruence.Targets
