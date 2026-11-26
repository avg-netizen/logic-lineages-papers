module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.Targets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof
/-- Old reflexivity is actually retained at the new common checker, not assumed. -/
def InternalReflexivity : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (accepted I.qctag I.ctag I.atag index fuel t t (reflexivityCertificate I.ctag I.reflexivityTag t))))
/-- Two actual MPs and paid retained reflexivity produce the reversed equality. -/
def InternalSymmetry : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u cert index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (accepted I.qctag I.ctag I.atag index fuel t u cert)
     (accepted I.qctag I.ctag I.atag index fuel u t
      (symmetryCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag t u cert))))))
/-- Four actual MPs compose input equalities through symmetry and original
right replacement, at the identical runtime and actual common checker. -/
def InternalTransitivity : Prop := ∀ n (p : Program n) (old a : Program 1) (x : Program 3)
 (I : Installation p old a x), ∀ ctx (t u v first second index fuel : Term ctx),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (RawReflexivityDispatcher.valid I.vtag v)
     (.imp (accepted I.qctag I.ctag I.atag index fuel t u first)
      (.imp (accepted I.qctag I.ctag I.atag index fuel u v second)
       (accepted I.qctag I.ctag I.atag index fuel t v
        (transitivityCertificate I.mpTag I.qtag I.reflexivityTag I.ctag I.atag t u v first second))))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityComposition.Targets
