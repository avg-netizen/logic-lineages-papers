module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxNodes
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxCalculation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowPRChildTags GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence



open HistoryRuleSuffix

open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof
def Source : Prop :=
 ∀ (f : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF0 pR : Program 1) (pCK : Program 2) (box : Program 6) (c : Code),
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 Actual pF pR outer c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∀ (carrierTag peelTag baseProducerTag : Nat),
 (nodes root)[carrierTag]? = some ⟨6,CurrentStructuralProducerInventory.carrier f lhs rhs t old a baseX pF0⟩ →
 (nodes root)[peelTag]? = some ⟨3,RuntimeOffsetAugmentationProducer.program⟩ →
 (nodes root)[baseProducerTag]? = some ⟨2,CurrentStructuralProducerCompiler.compile pF0⟩ →
 ∃ bound : Nat, ∀ ctx (value fuel : Term ctx),
 let K := tags I.previous
 let U := S pF pR outer
 Nonempty (Derivation U (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U
  (accepted I.currentK.coreTag I.currentK.verifierTag (Term.numeral (Encodable.encode c)) fuel
   (CurrentStructuralProducerCore.calculation K 6 (value ::ᵥ nil))
   (RetainedBaseSourceCalculation.certificate K pF0 pCK box outer peelTag baseProducerTag value)))

theorem exactSource : Source := by
 intro f lhs rhs k t old a baseX pF0 pR pCK box c
 dsimp only
 intro hA hbase I carrierTag peelTag baseProducerTag hcarrier hpeel hproducer
 let pF := GorbowNamedInternalProvability.augment (GorbowNamedInternalProvability.augment pF0 pCK) box
 let outer := CumulativePropositionalSource.verifier f lhs rhs old a baseX
 let root := CumulativePropositionalSource.root f lhs rhs pF pR old a baseX
 let U := S pF pR outer
 let K := tags I.previous
 let inner := GorbowNamedInternalProvability.augment pF0 pCK
 have incl := CumulativePropositionalSource.SeedSourceProof.inclusion f lhs rhs pF pR old a baseX
 obtain ⟨h6,h8,h10,h12⟩ := BoxNodes.nodes f lhs rhs t old a baseX pF0 pR pCK box
 obtain ⟨pb,hP⟩ := RuntimeOffsetAugmentationProducer.SourceEndpoint.exactSource f lhs rhs k t old a baseX pF pR c hA hbase I
 obtain ⟨sb,hS⟩ := CurrentStructuralProducerCore.StatementChecks.exactSource f lhs rhs k t old a baseX pF pR c hA hbase I
 refine ⟨pb+sb,?_⟩
 intro ctx value fuel hguard
 let index : Term ctx := Term.numeral (Encodable.encode c)
 obtain ⟨hg⟩ := hguard
 obtain ⟨hlp⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd U pb sb fuel
 obtain ⟨hls⟩ := CurrentRecursionProducerCore.GuardBound.lowerAdd U sb pb fuel
 have he : sb+pb = pb+sb := Nat.add_comm _ _
 rw [he] at hls
 have hpg := Derivation.mp hlp hg
 have hsg := Derivation.mp hls hg
 obtain ⟨hp6⟩ := hP 5 pF outer 6 peelTag h6 hpeel ctx value fuel
 obtain ⟨hp8⟩ := hP 6 inner box 8 peelTag h8 hpeel ctx value fuel
 obtain ⟨hp10⟩ := hP 2 pF0 pCK 10 peelTag h10 hpeel ctx value fuel
 have h68 := Derivation.mp hp6 hpg
 have h810 := Derivation.mp hp8 hpg
 have h1012 := Derivation.mp hp10 hpg
 have hbaseCalc := hS 1 pF0 carrierTag hcarrier 1 pF0 (.here pF0 rfl) 12 baseProducerTag h12 hproducer ctx (value ::ᵥ nil) fuel ⟨hsg⟩
 have hv := fun tag G => RetainedBaseSourceCalculation.AlgebraProof.rawValid root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I G tag value
 have h610 := RetainedBaseSourceCalculation.AlgebraProof.join root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I U incl
  (RetainedBaseSourceCalculation.rawCall K 6 value) (RetainedBaseSourceCalculation.rawCall K 8 value) (RetainedBaseSourceCalculation.rawCall K 10 value) _ _ index fuel
  (hv 6) (hv 8) (hv 10) ⟨h68⟩ ⟨h810⟩
 have h612 := RetainedBaseSourceCalculation.AlgebraProof.join root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I U incl
  (RetainedBaseSourceCalculation.rawCall K 6 value) (RetainedBaseSourceCalculation.rawCall K 10 value) (RetainedBaseSourceCalculation.rawCall K 12 value) _ _ index fuel
  (hv 6) (hv 10) (hv 12) h610 ⟨h1012⟩
 have hvout := fun G => CorrectedAugmentationErasure.AlgebraProof.rawValid root f lhs rhs t old a
  (SaturatedAxiomLeaf.saturated baseX) I G (call 12 (value ::ᵥ nil))
 have hfinal := RetainedBaseSourceCalculation.AlgebraProof.join root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX) I U incl
  (RetainedBaseSourceCalculation.rawCall K 6 value) (RetainedBaseSourceCalculation.rawCall K 12 value)
  (LiteralNumeralPrefix.numeralCall K.numeralTag (call 12 (value ::ᵥ nil))) _ _ index fuel
  (hv 6) (hv 12) hvout h612 hbaseCalc
 obtain ⟨he68⟩ := RetainedBaseSourceCalculation.SymbolicProof.peel root 6 pF outer h6 value
 obtain ⟨he810⟩ := RetainedBaseSourceCalculation.SymbolicProof.peel root 8 inner box h8 value
 obtain ⟨he1012⟩ := RetainedBaseSourceCalculation.SymbolicProof.peel root 10 pF0 pCK h10 value
 have he612 := Logic.trans _ _ _ he68 (Logic.trans _ _ _ he810 he1012)
 have he126 := Support.equalitySymmetry _ _ he612
 have hnum := HistoryLookup.DestructorProof.unaryCallCongruence K.numeralTag _ _ he126
 have hformula := CurrentCompositionCertificate.CodecProof.binary root K.ctag K.atag K.ctag K.atag 0
  I.previous.current.h_ctag I.previous.current.h_atag I.previous.current.h_ctag I.previous.current.h_atag
  (RetainedBaseSourceCalculation.rawCall K 6 value) (RetainedBaseSourceCalculation.rawCall K 6 value) _ _ (.logical (.reflexive _)) hnum
 have hout := CurrentStructuralProducerCore.CoreTools.transport root f lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)
  I U incl index fuel _ _ _ _ hformula ⟨.logical (.reflexive _)⟩ hfinal
 exact hout

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxCalculation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261117.InstalledLiteralBinaryProducer.BoxCalculation
