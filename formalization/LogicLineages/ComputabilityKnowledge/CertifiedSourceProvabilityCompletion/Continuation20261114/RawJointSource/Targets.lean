module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- Simultaneous, not sequential replacement: ONE actual source retains CK,
the original producer and all six packages while both original certificate
families are internally accepted. Both leaves are refined before choosing
pF/pR. Runtime quantifiers follow all witnesses. The two installed interfaces
share the actual verifier, codec and validator addresses. General coherent
computation quotation and HB3 remain open. -/
def OneUniformSource : Prop :=
 ∃ (old oldA : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 ∃ I : RawReflexivityCertificate.Installation
   (root pF pR old oldA baseX) old (RawAddZero.arithmeticLeaf oldA)
   (SaturatedAxiomLeaf.saturated baseX),
 ∃ J : RawAddZeroCertificate.Installation
   (root pF pR old oldA baseX) (ReflexivitySource.logical old) oldA
   (SaturatedAxiomLeaf.saturated baseX),
 I.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 J.utag = I.utag ∧ J.ptag = I.ptag ∧ J.ctag = I.ctag ∧
 J.atag = I.atag ∧ J.vtag = I.vtag ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate oldA v = HistoryDispatcher.arithmeticFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (ReflexivitySource.logical old) (RawAddZero.arithmeticLeaf oldA)
  (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 ReflexivityPackages.Packages old (RawAddZero.arithmeticLeaf oldA) baseX offset pF pR c mtag xtag ∧
 ∀ ctx (raw index fuel : Term ctx),
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
    (RawAddZeroCertificate.certificate J.ctag J.qtag raw))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.Targets
