module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CurrentInstallationProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
theorem installed (old ar : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (hall : ∀ q ∈ currentItems old ar x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 ∃ K : UniformClosedPropositionalCertificate.Installation p old ar x false,
 ∃ S : UniformClosedPropositionalCertificate.Installation p old ar x true,
 K.coreTag = S.coreTag ∧ K.iteratorTag = S.iteratorTag := by
 obtain ⟨constructorK,h_constructorK⟩ := hall (⟨3,UniformClosedPropositional.lineConstructor false⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨constructorS,h_constructorS⟩ := hall (⟨3,UniformClosedPropositional.lineConstructor true⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨ptag,h_ptag⟩ := hall (⟨2,HistoryCodec.pair⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨ctag,h_ctag⟩ := hall (⟨2,HistoryCodec.cons⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨atag,h_atag⟩ := hall (⟨2,HistoryAppend.append⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨fval,h_fval⟩ := hall (⟨2,LiteralSyntaxValidator.formulaValidator⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨stag,h_stag⟩ := hall (⟨2,LiteralSyntaxScan.scanCode⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨lineTag,h_lineTag⟩ := hall (⟨1,LiteralSyntaxValidator.lineValidator⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨logicalTag,h_logicalTag⟩ := hall (⟨1,UniformClosedPropositional.logicalLeaf old⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨dispatcherTag,h_dispatcherTag⟩ := hall (⟨4,UniformClosedPropositionalCertificate.dispatcher old ar x⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨iteratorTag,h_iteratorTag⟩ := hall (⟨4,SixSol20261112.HistoryMachine.iterator (UniformClosedPropositionalCertificate.kernel old ar x)⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨coreTag,h_coreTag⟩ := hall (⟨5,UniformClosedPropositionalCertificate.checker old ar x⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨verifierTag,h_verifierTag⟩ := hall (⟨5,UniformClosedPropositionalCertificate.verifier old ar x⟩ : Packed) (by simp only [currentItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 let K : UniformClosedPropositionalCertificate.Installation p old ar x false :=
  {constructorTag := constructorK,h_constructorTag := h_constructorK,ptag,ctag,atag,fval,stag,lineTag,logicalTag,dispatcherTag,iteratorTag,coreTag,verifierTag,h_ptag,h_ctag,h_atag,h_fval,h_stag,h_lineTag,h_logicalTag,h_dispatcherTag,h_iteratorTag,h_coreTag,h_verifierTag}
 let S : UniformClosedPropositionalCertificate.Installation p old ar x true :=
  {constructorTag := constructorS,h_constructorTag := h_constructorS,ptag,ctag,atag,fval,stag,lineTag,logicalTag,dispatcherTag,iteratorTag,coreTag,verifierTag,h_ptag,h_ctag,h_atag,h_fval,h_stag,h_lineTag,h_logicalTag,h_dispatcherTag,h_iteratorTag,h_coreTag,h_verifierTag}
 exact ⟨K,S,rfl,rfl⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CurrentInstallationProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CumulativePropositionalSource.CurrentInstallationProof
