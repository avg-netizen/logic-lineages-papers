module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
/-- ONE source precedes all raw/index/fuel quantifiers. Full Retained (including
CK and original producer) and all six prior packages remain at its identical
witnesses. Actual finite interface installation is a conclusion, not a premise.
The actual source verifier accepts the original raw singleton certificate under
its genuine internal term-validator antecedent. No term-template choice,
external validity premise, coherent computation or HB3 is asserted. -/
def OneUniformSource : Prop :=
 ∃ (old a : Program 1) (baseX : Program 3) (offset : Nat),
 ∃ (pF pR : Program 1) (c : Code) (tagCK : Nat) (pCK : Program 2)
   (tagG : Nat) (pG : Program 6) (mtag xtag : Nat),
 ∃ I : RawReflexivityCertificate.Installation
   (ReflexivityInstalled.root pF pR old a baseX) old a (SaturatedAxiomLeaf.saturated baseX),
 I.utag = GorbowNamedInternalProvability.checkerTag pF ∧
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) ∧
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) ∧
 LiteralValidatedSource.Retained (ReflexivitySource.logical old) a
  (SaturatedAxiomLeaf.saturated baseX) offset pF pR c tagCK pCK tagG pG ∧
 ReflexivityPackages.Packages old a baseX offset pF pR c mtag xtag ∧
 ∀ ctx (raw index fuel : Term ctx),
 Nonempty (Derivation (S pF pR (ReflexivityInstalled.verifier old a baseX))
  (.imp (RawReflexivityDispatcher.valid I.vtag raw)
   (SixSol20261112.Fuel.success (GorbowNamedInternalProvability.checkerTag pF)
    index fuel .zero
    (.add (RawReflexivity.equalityValue I.ctag I.atag raw)
     (RawReflexivity.equalityValue I.ctag I.atag raw))
    (RawReflexivityCertificate.certificate I.ctag I.qtag raw))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.Targets
