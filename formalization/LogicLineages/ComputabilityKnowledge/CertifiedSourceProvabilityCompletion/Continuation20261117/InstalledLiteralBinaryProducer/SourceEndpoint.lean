module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.GraphProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxLiteral
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SourceEndpoint
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem bridge (f : Formula 1) (lhs rhs : Term 1) (old a : Program 1) (baseX : Program 3)
 (pF0 pR : Program 1) (pCK : Program 2) (pG : Program 6) (c : Code)
 (hA : Actual (selected f lhs rhs old a baseX pF0 pCK pG) pR (CumulativePropositionalSource.verifier f lhs rhs old a baseX) c)
 (hbase : ∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root f lhs rhs (selected f lhs rhs old a baseX pF0 pCK pG) pR old a baseX)
  f lhs rhs CurrentNamedHeaderCertificate.template old a (SaturatedAxiomLeaf.saturated baseX))
 (carrierTag peelTag baseProducerTag producerTag : Nat)
 (hcarrier : (nodes (CumulativePropositionalSource.root f lhs rhs (selected f lhs rhs old a baseX pF0 pCK pG) pR old a baseX))[carrierTag]? =
  some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs CurrentNamedHeaderCertificate.template old a baseX pF0⟩)
 (hpeel : (nodes (CumulativePropositionalSource.root f lhs rhs (selected f lhs rhs old a baseX pF0 pCK pG) pR old a baseX))[peelTag]? =
  some ⟨3,RuntimeOffsetAugmentationProducer.program⟩)
 (hbaseProducer : (nodes (CumulativePropositionalSource.root f lhs rhs (selected f lhs rhs old a baseX pF0 pCK pG) pR old a baseX))[baseProducerTag]? =
  some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩)
 (hproducer : (nodes (CumulativePropositionalSource.root f lhs rhs (selected f lhs rhs old a baseX pF0 pCK pG) pR old a baseX))[producerTag]? = some ⟨5,program pF0⟩) :
 let t := CurrentNamedHeaderCertificate.template
 let pF := selected f lhs rhs old a baseX pF0 pCK pG
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 ∃ bound : Nat, ∀ ctx (r s fuel : Term ctx),
 let K := tags R.previous
 let U := S pF pR outer
 let box := InstalledProducerExtra.container pG (extra f lhs rhs old a baseX pF0)
 Nonempty (Derivation U (orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U (accepted R.currentK.coreTag R.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
  (equalValue K.ctag K.atag (RetainedBaseLiteralBinary.rawBinary K r s)
   (LiteralNumeralPrefix.numeralCall K.numeralTag (GorbowBooleanTruth.binaryCodeTerm 0 r s)))
  (call producerTag (inputs pF0 pCK box outer r s)))) := by
 let t := CurrentNamedHeaderCertificate.template
 let pF := selected f lhs rhs old a baseX pF0 pCK pG
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let R := CurrentPublishedProvabilityIntroduction.RuntimeRebase.shared root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I
 let U := S pF pR outer
 let box := InstalledProducerExtra.container pG (extra f lhs rhs old a baseX pF0)
 have incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old a baseX
 obtain ⟨bound,hliteral⟩ := BoxLiteral.exactLiteral f lhs rhs old a baseX pF0 pR pCK box c hA hbase I
  carrierTag peelTag baseProducerTag hcarrier hpeel hbaseProducer
 refine ⟨bound,?_⟩
 intro ctx r s fuel
 dsimp only
 intro hg
 obtain ⟨hl⟩ := hliteral ctx r s fuel hg
 obtain ⟨hc⟩ := CurrentStructuralProducerCore.CoreTools.project U _ _ _ fuel _ _ ⟨hl⟩
 obtain ⟨he⟩ := GraphProof.exactGraph f lhs rhs old a baseX pF0 pR pCK pG I peelTag baseProducerTag producerTag
  hpeel hbaseProducer hproducer ctx r s
 obtain ⟨heS⟩ := GorbowTheoryProofProof.monotonicity _ U incl ctx _ ⟨he⟩
 obtain ⟨hout⟩ := CurrentImplicationCertificate.RebaseProof.coreCode U [] R.currentK.coreTag
  (Term.numeral (Encodable.encode c)) fuel _ _ _ (.base (Support.equalitySymmetry _ _ heS)) (.base hc)
 obtain ⟨ha⟩ := CurrentImplicationCertificate.AlgebraSupport.acceptedOfCore root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) R U incl [] _ _
  (Term.numeral (Encodable.encode c)) fuel hout
 exact ⟨ha.finish⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SourceEndpoint
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.SourceEndpoint
