module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual closed-term validator closure under original successor prefix. -/
def InternalSuccessorValidity : Prop := ∀ n (p : Program n) (vtag ptag ctag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (RawReflexivityDispatcher.valid vtag (RawSuccReplace.succValue ctag raw))))
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
      (.add (inputRaw I.ctag I.atag t u) (inputRaw I.ctag I.atag t u)) cert) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
       (.add (outputRaw I.ctag I.atag t u) (outputRaw I.ctag I.atag t u))
       (certificate I.mpTag I.replaceTag I.qtag I.ctag I.atag t u cert)) (.succ .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccCongruence.Targets
