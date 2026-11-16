module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.PrimitiveProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.RegistryProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem installed {arity k m : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3)
 (I : CumulativePropositionalSource.JointInstallation p installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX))
 (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (extraTag oldExtraTag carrierTag : Nat)
 (he : (nodes p)[extraTag]? = some ⟨6,extendedExtra installed lhs rhs t old a baseX base step B G⟩)
 (ho : (nodes p)[oldExtraTag]? = some ⟨6,CumulativePropositionalSource.extra installed lhs rhs t old a baseX⟩)
 (hc : (nodes p)[carrierTag]? = some ⟨6,producerCarrier base step B G⟩)
 (hall : ∀ q ∈ producerItems base step B G, ∃ (tag : Nat), (nodes p)[tag]? = some q) :
 Nonempty (Installation p installed lhs rhs t old a baseX base step B G) := by
 obtain ⟨qTag,hq⟩ := hall (⟨m+1,.recursion base step⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨BTag,hB⟩ := hall (⟨m+1,B⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨GTag,hG⟩ := hall (⟨m+3,G⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨publicTag,hpublic⟩ := hall (⟨m+2,CurrentRecursionProducerProgram.program base step B G⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨accumulatorTag,haccumulator⟩ := hall (⟨m+2,CurrentRecursionProducerProgram.accumulator base step B G⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨baseTag,hbaseProducer⟩ := hall (⟨m+1,CurrentRecursionBaseProgram.program base B⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨formulaTag,hformula⟩ := hall (⟨m+2,CurrentCalculationFormulaProgram.program (.recursion base step)⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨stepTag,hstepProducer⟩ := hall (⟨m+2,CurrentRecursionStepProgram.program base step G⟩ : Packed) (by simp only [producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 have hbase := GorbowPRSubtree.Proof.lookupTransport arity p qTag ⟨m+1,.recursion base step⟩ 1 ⟨m,base⟩ hq
  (GorbowPRChildTags.Proof.recursionBase m base step)
 have hstep := SixSol20261112.Fuel.Equations.recursionStepChild p qTag base step hq
 let BJ := PrimitiveProof.baseTags I base qTag BTag
 let SJ := PrimitiveProof.stepTags I base qTag GTag
 let N : CurrentRecursionProducerProgram.GraphNodes p base step B G :=
  {publicTag,accumulatorTag,baseTag,formulaTag,stepTag,
   mpTag := I.previous.previous.previous.previous.previous.mpTag,
   hpublic,haccumulator,hbase := hbaseProducer,hformula,hstep := hstepProducer,
   hmp := I.previous.previous.previous.previous.previous.hmp}
 exact ⟨{
   extraTag,oldExtraTag,carrierTag,qTag,BTag,GTag,BJ,SJ,producer := N,
   hExtra := he,hOldExtra := ho,hCarrier := hc,hItems := hall,hQ := hq,hBase := hbase,hStep := hstep,hB,hG,
   baseInstallation := PrimitiveProof.baseInstalled p installed lhs rhs t old a _ I base B qTag BTag hbase hB,
   stepInstallation := PrimitiveProof.stepInstalled p installed lhs rhs t old a _ I base step G qTag GTag hq hstep hG,
   baseAddress := rfl,baseChildAddress := rfl,recursionAddress := rfl,stepAddress := rfl,stepChildAddress := rfl,mpAddress := rfl}⟩

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.RegistryProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerSource.RegistryProof
