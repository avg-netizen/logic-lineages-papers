module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence

/-- A genuine noncircular newly selected source, retaining CK and the given
producer, installing the base-only compiler inventory and fixed peel producer.
Actual source index and uniform bound are chosen after finite AST construction.
No compiler of final pF, constructor equality, or certificate success is assumed. -/
def Installed : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3),
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 UniversalVerifier (CumulativePropositionalSource.verifier f lhs rhs old a baseX) →
 ∀ (pCK : Program 2), GorbowUniformCommonKnowledge.CodeProgram pCK →
 ∀ (pG : Program 6),
 ∃ (pF0 pR : Program 1) (c : Code) (tagCK tagG carrierTag peelTag baseProducerTag : Nat),
 let pF := selected f lhs rhs t old a baseX pF0 pCK pG
 let q := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 GorbowSelectedDistribution.Calibrated pF0 pR ∧
 Actual pF pR q c ∧ SourceBaseCompletion.SyntaxAdequate pF pR q ∧
 GorbowUniformCommonKnowledge.RegistryInstall pF pR q tagCK pCK ∧
 GorbowUniformCommonKnowledge.FixedPointFor pF pR q c tagCK ∧
 InstalledProducer.RegistryInstall pF pR q tagG pG ∧
 (nodes root)[6]? = some ⟨1,augmented pF q⟩ ∧
 (nodes root)[8]? = some ⟨1,pF⟩ ∧
 (nodes root)[10]? = some ⟨1,GorbowNamedInternalProvability.augment pF0 pCK⟩ ∧
 (nodes root)[12]? = some ⟨1,pF0⟩ ∧
 (nodes root)[carrierTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ ∧
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ ∧
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ ∧
 CurrentStructuralProducerInventory.InstalledAt root f lhs rhs t old a baseX 12 baseProducerTag pF0 ∧
 ∃ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ ctx (value fuel : Term ctx),
 let K := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let guard := SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel
 Nonempty (Derivation (S pF pR q) (.imp guard
  (AcceptedPeel K I.currentK.coreTag I.currentK.verifierTag peelTag 6 pF q index value fuel))) ∧
 Nonempty (Derivation (S pF pR q) (.imp guard
  (AcceptedPeel K I.currentK.coreTag I.currentK.verifierTag peelTag 8
   (GorbowNamedInternalProvability.augment pF0 pCK)
   (InstalledProducerExtra.container pG (extra f lhs rhs t old a baseX pF0)) index value fuel))) ∧
 Nonempty (Derivation (S pF pR q) (.imp guard
  (AcceptedPeel K I.currentK.coreTag I.currentK.verifierTag peelTag 10 pF0 pCK index value fuel)))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.RetainedBaseProducerInstallation.Targets
