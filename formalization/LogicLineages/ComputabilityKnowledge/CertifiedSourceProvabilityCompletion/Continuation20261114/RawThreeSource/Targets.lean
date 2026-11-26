module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawThreeSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawThreeSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Simultaneous, not sequential replacement: ONE actual source retains CK,
the original producer and all six packages while all three original certificate
families are internally accepted. All leaves are refined before choosing
pF/pR. Runtime quantifiers follow all witnesses. The three installed interfaces
share the actual verifier, codec and validator addresses. General coherent
computation quotation and HB3 remain open. -/
def OneUniformSource : Prop :=
 ∃ (old oldA : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 ∃ I : RawReflexivityCertificate.Installation
   (root pF pR old oldA baseX) old (RawCumulativeArithmetic.arithmetic oldA)
   (SaturatedAxiomLeaf.saturated baseX),
 ∃ J : RawCumulativeArithmetic.CertificateInstallation
   (root pF pR old oldA baseX) (ReflexivitySource.logical old) oldA
   (SaturatedAxiomLeaf.saturated baseX),
 ∃ K : RawAddSuccCertificate.Installation
   (root pF pR old oldA baseX) (ReflexivitySource.logical old) (RawAddZero.arithmeticLeaf oldA)
   (SaturatedAxiomLeaf.saturated baseX),
 I.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 J.utag = I.utag ∧ J.ptag = I.ptag ∧ J.ctag = I.ctag ∧
 J.atag = I.atag ∧ J.vtag = I.vtag ∧
 K.utag = I.utag ∧ K.ptag = I.ptag ∧ K.ctag = I.ctag ∧
 K.atag = I.atag ∧ K.vtag = I.vtag ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate oldA v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (ReflexivitySource.logical old) (RawCumulativeArithmetic.arithmetic oldA)
  (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 ReflexivityPackages.Packages old (RawCumulativeArithmetic.arithmetic oldA) baseX offset pF pR c mtag xtag ∧
 ∀ ctx (raw rawB index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (SixSol20261112.Fuel.success (GorbowNamedInternalProvability.checkerTag pF)
    index fuel .zero
    (.add (RawReflexivity.equalityValue I.ctag I.atag raw)
     (RawReflexivity.equalityValue I.ctag I.atag raw))
    (RawReflexivityCertificate.certificate I.ctag I.qtag raw)))) ∧
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid J.vtag raw)
   (SixSol20261112.Fuel.success (GorbowNamedInternalProvability.checkerTag pF)
    index fuel .zero
    (.add (RawAddZero.equalityValue J.ctag J.atag raw)
     (RawAddZero.equalityValue J.ctag J.atag raw))
    (RawCumulativeArithmetic.certificate J.ctag J.qtag raw))))
 ∧
 Nonempty (Derivation (S pF pR (verifier old oldA baseX))
  (.imp (RawReflexivityDispatcher.valid K.vtag raw)
   (.imp (RawReflexivityDispatcher.valid K.vtag rawB)
    (SixSol20261112.Fuel.success (GorbowNamedInternalProvability.checkerTag pF)
     index fuel .zero
     (.add (RawAddSucc.equalityValue K.ctag K.atag raw rawB)
      (RawAddSucc.equalityValue K.ctag K.atag raw rawB))
     (RawAddSuccCertificate.certificate K.ctag K.qtag raw rawB)))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawThreeSource.Targets
