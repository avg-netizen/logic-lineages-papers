module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Actual internal closed raw-term validity under original addition prefix. -/
def InternalAdditionValidity : Prop := ∀ n (p : Program n) (vtag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (t u : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag t)
   (.imp (RawReflexivityDispatcher.valid vtag u)
    (RawReflexivityDispatcher.valid vtag (addRaw ctag atag t u)))))
/-- Base computation t+0=t at precisely the newest shared checker. -/
def InternalBase : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
    (addRaw I.ctag I.atag t (zeroRaw I.ctag)) t (RawCumulativeArithmetic.certificate I.ctag I.zeroTag t))))
/-- Actual certificate step t+u=v ⇒ t+succ(u)=succ(v), with genuine
internal input computation and validity antecedents, not assumed step success. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (RawReflexivityDispatcher.valid I.vtag v)
     (.imp (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel (addRaw I.ctag I.atag t u) v cert)
      (RawEqualityComposition.accepted I.qctag I.ctag I.atag index fuel
       (addRaw I.ctag I.atag t (succRaw I.ctag u)) (succRaw I.ctag v)
       (stepCertificate I.mpTag I.qtag I.replaceTag I.reflexivityTag I.addTag I.ctag I.atag t u v cert)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAdditionComputation.Targets
