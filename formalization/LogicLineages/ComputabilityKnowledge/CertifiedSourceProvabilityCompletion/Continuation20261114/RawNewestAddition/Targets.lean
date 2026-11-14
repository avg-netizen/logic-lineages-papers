module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAddition.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAddition.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
/-- Base computation t+0=t at the actual common multiplication-plus-addition checker. -/
def InternalBase : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
    (addRaw I.consTag I.appendTag t (zeroRaw I.consTag)) t (RawCumulativeArithmetic.certificate I.consTag I.zeroTag t))))
/-- Actual certificate step t+u=v ⇒ t+succ(u)=succ(v), with genuine
internal input computation and validity antecedents, not assumed step success. -/
def InternalStep : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.validatorTag t)
   (.imp (RawReflexivityDispatcher.valid I.validatorTag u)
    (.imp (RawReflexivityDispatcher.valid I.validatorTag v)
     (.imp (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel (addRaw I.consTag I.appendTag t u) v cert)
      (RawEqualityComposition.accepted I.qctag I.consTag I.appendTag index fuel
       (addRaw I.consTag I.appendTag t (succRaw I.consTag u)) (succRaw I.consTag v)
       (stepCertificate I.mpTag I.equalityLineTag I.replaceTag I.reflexivityTag I.addTag I.consTag I.appendTag t u v cert)))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNewestAddition.Targets
