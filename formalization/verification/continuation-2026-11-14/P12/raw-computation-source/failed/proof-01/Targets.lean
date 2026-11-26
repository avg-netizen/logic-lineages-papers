module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- ONE source precedes every raw/runtime/certificate input. Full Retained,
all six original packages, all four original singleton families and real
two-MP successor congruence coexist at the exact same checker/MP witnesses.
General coherent computation quotation and HB3 remain open. -/
def OneUniformSource : Prop :=
 ∃ (old oldA : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (xtag : Nat),
 ∃ I : RawSuccCongruence.Installation (root pF pR old oldA baseX) old (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX),
 ∃ J : RawCumulativeArithmetic.CertificateInstallation (root pF pR old oldA baseX) (logical old) oldA (SaturatedAxiomLeaf.saturated baseX),
 ∃ K : RawAddSuccCertificate.Installation (root pF pR old oldA baseX) (logical old) (RawAddZero.arithmeticLeaf oldA) (SaturatedAxiomLeaf.saturated baseX),
 I.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 J.utag = I.utag ∧ J.ptag = I.ptag ∧ J.ctag = I.ctag ∧ J.atag = I.atag ∧ J.vtag = I.vtag ∧
 K.utag = I.utag ∧ K.ptag = I.ptag ∧ K.ctag = I.ctag ∧ K.atag = I.atag ∧ K.vtag = I.vtag ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate oldA v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (logical old) (arithmetic oldA) (SaturatedAxiomLeaf.saturated baseX)
  offset pF pR c tagCK pCK tagG pG ∧
 Packages old oldA baseX offset pF pR c I.mpTag xtag ∧
 ∀ ctx (t u cert index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawReflexivity.equalityValue I.ctag I.atag t) (RawReflexivity.equalityValue I.ctag I.atag t))
    (RawCumulativeLogical.certificate I.ctag I.qtag t)))) ∧
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid J.vtag t)
   (SixSol20261112.Fuel.success I.utag index fuel .zero
    (.add (RawAddZero.equalityValue J.ctag J.atag t) (RawAddZero.equalityValue J.ctag J.atag t))
    (RawCumulativeArithmetic.certificate J.ctag J.qtag t)))) ∧
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid K.vtag t)
   (.imp (RawReflexivityDispatcher.valid K.vtag u)
    (SixSol20261112.Fuel.success I.utag index fuel .zero
     (.add (RawAddSucc.equalityValue K.ctag K.atag t u) (RawAddSucc.equalityValue K.ctag K.atag t u))
     (RawAddSuccCertificate.certificate K.ctag K.qtag t u))))) ∧
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (SixSol20261112.Fuel.success I.utag index fuel .zero
     (.add (RawSuccReplace.formulaValue I.ctag I.atag t u) (RawSuccReplace.formulaValue I.ctag I.atag t u))
     (RawSuccReplaceCertificate.certificate I.ctag I.replaceTag t u))))) ∧
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid I.vtag t)
   (.imp (RawReflexivityDispatcher.valid I.vtag u)
    (.imp (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (RawSuccCongruence.inputRaw I.ctag I.atag t u) (RawSuccCongruence.inputRaw I.ctag I.atag t u)) cert) (.succ .zero))
     (.equal (LiteralCheckerAcceptance.coreCall I.qctag index fuel .zero
      (.add (RawSuccCongruence.outputRaw I.ctag I.atag t u) (RawSuccCongruence.outputRaw I.ctag I.atag t u))
      (RawSuccCongruence.certificate I.mpTag I.replaceTag I.qtag I.ctag I.atag t u cert)) (.succ .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.Targets
