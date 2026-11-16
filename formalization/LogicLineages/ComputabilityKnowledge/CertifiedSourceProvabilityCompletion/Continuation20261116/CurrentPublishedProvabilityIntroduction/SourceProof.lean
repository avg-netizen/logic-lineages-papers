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
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource.RetainedExtraProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentQuantifierLogicalSource.BundleProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCheckerSuccessCertificate.BridgeProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.SourceEndpoint
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentExistentialIntroductionProgram.BundleProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SourceEndpoint
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.BundleProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SourceProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof GorbowPublishedDCB SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open CumulativePropositionalSource
theorem onePublishedSource : Targets.OnePublishedIntroductionSource := by
 intro f lhs rhs k t ht
 dsimp only
 let Q : Program 1 → Program 1 → Program 3 → Program 5 :=
  fun old a baseX => CumulativePropositionalSource.verifier f lhs rhs old a baseX
 obtain ⟨rawOld,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,publishedExtraTag,hraw,hold,ha,hbase,hret,hPublishedExtra⟩ :=
  CurrentQuantifierLogicalSource.RetainedExtraProof.retainedWithExtra f lhs rhs (fun rawOld a baseX => CurrentPublishedProvabilityIntroduction.extra f lhs rhs t rawOld a baseX)
 let old := CurrentQuantifierLogicalSource.selectedOld rawOld
 obtain ⟨⟨transformExtraTag,hTransformExtra⟩,⟨publishedTag,hPublished⟩⟩ := BundleProof.unpack
  (root f lhs rhs pF pR old a baseX) f lhs rhs t rawOld a baseX publishedExtraTag hPublishedExtra
 obtain ⟨⟨qetag,hqe⟩,⟨transformTag,hTransform⟩⟩ := CurrentExistentialIntroductionProgram.BundleProof.unpack
  (root f lhs rhs pF pR old a baseX) f lhs rhs t rawOld a baseX transformExtraTag hTransformExtra
 obtain ⟨⟨etag,he⟩,hItems⟩ := CurrentQuantifierLogicalSource.BundleProof.unpack
  (root f lhs rhs pF pR old a baseX) f lhs rhs t rawOld a baseX qetag hqe
 obtain ⟨oldExtraTag,inventoryTag,ho,hInventory⟩ :=
  CurrentStructuralProducerSource.BundleProof.unpack (root f lhs rhs pF pR old a baseX) f lhs rhs t Q old a baseX etag he
 obtain ⟨mtag,btag,I0,hK,hS,hcore,hiter,hb,hm⟩ := InstallationProof.installed f lhs rhs t old a baseX pF pR oldExtraTag ho
 let I := RuntimeRebase.shared (root f lhs rhs pF pR old a baseX) f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I0
 obtain ⟨cl,hcl⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.lineConstructor false⟩ (by simp [CurrentQuantifierLogicalSource.items])
 obtain ⟨dl,hdl⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.lineConstructor true⟩ (by simp [CurrentQuantifierLogicalSource.items])
 obtain ⟨cs,hcs⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor false⟩ (by simp [CurrentQuantifierLogicalSource.items])
 obtain ⟨ds,hds⟩ := hItems ⟨2,OriginalQuantifierLogicalProducers.singletonConstructor true⟩ (by simp [CurrentQuantifierLogicalSource.items])
 let N : CurrentExistentialIntroductionProgram.LogicalInterface.Nodes (root f lhs rhs pF pR old a baseX) :=
  { lineTag := fun b => if b then dl else cl
    singletonTag := fun b => if b then ds else cs
    hline := fun b => by cases b with | false => exact hcl | true => exact hdl
    hsingle := fun b => by cases b with | false => exact hcs | true => exact hds }
 have hTransformer := CurrentExistentialIntroductionProgram.SourceEndpoint.bridge f lhs rhs t rawOld a baseX pF pR I N transformTag hTransform
 have hPublishedBridge := SourceEndpoint.bridge f lhs rhs t rawOld a baseX pF pR c I0 N transformTag publishedTag hTransform hPublished
 obtain ⟨evaluatorTag,producerTag,hEvaluator,hProducer⟩ := CurrentStructuralProducerSource.InventoryProof.rootPrograms
  (root f lhs rhs pF pR old a baseX) f lhs rhs t old a baseX (Q old a baseX) inventoryTag hInventory
 have hAll := CurrentStructuralProducerInventory.StatementChecks.exactInstallations 4
  (root f lhs rhs pF pR old a baseX) f lhs rhs k t old a baseX I 5 (Q old a baseX) inventoryTag hInventory
 obtain ⟨xtag,hpackages⟩ := PackageProof.packages f lhs rhs old a baseX offset pF pR c tagCK pCK tagG pG mtag hret hm
 have hA : Actual pF pR (verifier f lhs rhs old a baseX) c := hret.2.2.2.2.2.2.2.2.1
 have hchecker := GorbowNamedInternalProvability.Proof.exactCheckerTag 5 pF pR (Q old a baseX)
 have hbridge := CurrentCheckerSuccessCertificate.BridgeProof.bridge f lhs rhs t old a baseX pF pR c hA hbase I inventoryTag producerTag hInventory hProducer
 exact ⟨rawOld,a,baseX,offset,pF,pR,c,tagCK,pCK,tagG,pG,mtag,xtag,btag,etag,inventoryTag,evaluatorTag,producerTag,I,hK,hS,hcore,hiter,hold,ha,hbase,hb,hm,hret,hpackages,
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
  he,hInventory,hEvaluator,hProducer,hAll,hchecker,hbridge,hraw,⟨qetag,hqe⟩,hItems,
  ⟨transformExtraTag,transformTag,I.previous.previous.current.itag,I.previous.previous.current.predTag,
   I.previous.previous.current.vtag,hTransformExtra,hTransform,I.previous.previous.current.h_itag,
   I.previous.previous.current.h_predTag,I.previous.previous.current.h_vtag,hTransformer⟩,
  ⟨publishedExtraTag,publishedTag,hPublishedExtra,hPublished,hPublishedBridge⟩⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SourceProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SourceProof
