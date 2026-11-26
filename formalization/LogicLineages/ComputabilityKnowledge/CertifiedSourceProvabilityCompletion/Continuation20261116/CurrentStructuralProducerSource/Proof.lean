module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RetainedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.PackageProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CompilerCapabilityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.EqualityCapabilityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.FullFormulaCapabilityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.RetentionCapabilityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform13CapabilityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Uniform12CapabilityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.PropositionalCapabilityProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.AxiomSeedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.SeedTraceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionTraceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewCompositionConstructorProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewRecursionBaseTraceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.NewRecursionBaseConstructorProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.RetainedExtraProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.BundleProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.RegistryProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.EquationsProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.InventoryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.Proof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open CumulativePropositionalSource
theorem onePublishedSource : Targets.OnePublishedSource := by
 intro f lhs rhs k t ht n Q
 obtain ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,etag,hold,ha,hbase,hret,he⟩ :=
  CurrentRecursionProducerSource.RetainedExtraProof.retainedWithExtra f lhs rhs (fun old a baseX => extendedExtra f lhs rhs t Q old a baseX)
 obtain ⟨oldExtraTag,inventoryTag,ho,hInventory⟩ :=
  BundleProof.unpack (root f lhs rhs pF pR old a baseX) f lhs rhs t Q old a baseX etag he
 obtain ⟨mtag,btag,I,hK,hS,hcore,hiter,hb,hm⟩ := InstallationProof.installed f lhs rhs t old a baseX pF pR oldExtraTag ho
 obtain ⟨evaluatorTag,producerTag,hEvaluator,hProducer⟩ := InventoryProof.rootPrograms
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a baseX (Q old a baseX) inventoryTag hInventory
 have hAll := CurrentStructuralProducerInventory.StatementChecks.exactInstallations 4
  (root f lhs rhs pF pR old a baseX) f lhs rhs k t old a baseX I n (Q old a baseX) inventoryTag hInventory
 obtain ⟨xtag,hpackages⟩ := PackageProof.packages f lhs rhs old a baseX offset pF pR c tagCK pCK tagG pG mtag hret hm
 have hA : Actual pF pR (verifier f lhs rhs old a baseX) c := hret.2.2.2.2.2.2.2.2.1
 exact ⟨old,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,btag,etag,inventoryTag,evaluatorTag,producerTag,I,hK,hS,hcore,hiter,hold,ha,hbase,hb,hm,hret,hpackages,
  CompilerCapabilityProof.compiler f lhs rhs t ht old a baseX pF pR I,
  EqualityCapabilityProof.equality f lhs rhs t old a baseX pF pR I,
  FullFormulaCapabilityProof.fullFormula f lhs rhs t old a baseX pF pR I,
  RetentionCapabilityProof.retention f lhs rhs t old a baseX pF pR I,
  RetentionCapabilityProof.priorRetention f lhs rhs t old a baseX pF pR I,
  Uniform13CapabilityProof.uniform13 f lhs rhs t old a baseX pF pR I,
  Uniform12CapabilityProof.uniform12 f lhs rhs t old a baseX pF pR I,
  PropositionalCapabilityProof.propositional f lhs rhs t old a baseX pF pR I,
  AxiomSeedProof.seed f lhs rhs t old a baseX pF pR c hA hbase I,
  SeedProof.seeded f lhs rhs t old a baseX pF pR c hA hbase I,
  SeedTraceProof.trace f lhs rhs t old a baseX pF pR c I,
  NewCompositionTraceProof.exactTrace f lhs rhs t old a baseX pF pR c hA I,
  NewCompositionConstructorProof.exactConstructor f lhs rhs t old a baseX pF pR c hA hbase I,
  NewRecursionBaseTraceProof.exactTrace f lhs rhs t old a baseX pF pR c hA I,
  NewRecursionBaseConstructorProof.exactConstructor f lhs rhs t old a baseX pF pR c hA hbase I,
  he,hInventory,hEvaluator,hProducer,hAll⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerSource.Proof
