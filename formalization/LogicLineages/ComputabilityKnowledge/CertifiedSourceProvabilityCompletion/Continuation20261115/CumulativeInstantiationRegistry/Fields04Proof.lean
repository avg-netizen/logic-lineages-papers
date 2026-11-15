module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Fields03Proof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawUniversalCongruence
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence
theorem installed (old a : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items old a x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawUniversalCongruence.Installation p old a x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_ArithmeticTemplateEvaluation.installed old a x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨universalLineTag,huniversalLine⟩ := h (⟨2,RawUniversalReplace.lineConstructor⟩ : Packed) (by simp [items])
 obtain ⟨universalLogicalTag,huniversalLogical⟩ := h (⟨1,RawUniversalReplace.logicalLeaf (RawUniversalCongruence.previousLogical old)⟩ : Packed) (by simp [items])
 obtain ⟨universalDispatcherTag,huniversalDispatcher⟩ := h (⟨4,RawUniversalReplaceDispatcher.dispatcher (RawUniversalCongruence.previousLogical old) (RawMulNewestAddition.arithmetic a) x⟩ : Packed) (by simp [items])
 obtain ⟨universalIteratorTag,huniversalIterator⟩ := h (⟨4,SixSol20261112.HistoryMachine.iterator (RawUniversalReplaceCertificate.kernel (RawUniversalCongruence.previousLogical old) (RawMulNewestAddition.arithmetic a) x)⟩ : Packed) (by simp [items])
 obtain ⟨universalCoreTag,huniversalCore⟩ := h (⟨5,RawUniversalReplaceCertificate.checker (RawUniversalCongruence.previousLogical old) (RawMulNewestAddition.arithmetic a) x⟩ : Packed) (by simp [items])
 exact ⟨{
  toArithmetic := parent
  universalLineTag := universalLineTag
  huniversalLine := huniversalLine
  universalLogicalTag := universalLogicalTag
  huniversalLogical := huniversalLogical
  universalDispatcherTag := universalDispatcherTag
  huniversalDispatcher := huniversalDispatcher
  universalIteratorTag := universalIteratorTag
  huniversalIterator := huniversalIterator
  universalCoreTag := universalCoreTag
  huniversalCore := huniversalCore
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawUniversalCongruence
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawUniversalCongruence
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawEqualityInstantiationDispatcher
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher
theorem installed (a b : Term 1) (old arithmetic : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items a b old arithmetic x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationDispatcher.Installation p a b old arithmetic x) := by
 obtain ⟨qtag,hq⟩ := h (⟨1,RawEqualityInstantiation.line a b⟩ : Packed) (by simp [items])
 obtain ⟨ptag,hp⟩ := h (⟨2,HistoryCodec.pair⟩ : Packed) (by simp [items])
 obtain ⟨ctag,hc⟩ := h (⟨2,HistoryCodec.cons⟩ : Packed) (by simp [items])
 obtain ⟨atag,ha⟩ := h (⟨2,HistoryAppend.append⟩ : Packed) (by simp [items])
 obtain ⟨vtag,hv⟩ := h (⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ : Packed) (by simp [items])
 obtain ⟨ftag,hf⟩ := h (⟨2,LiteralSyntaxValidator.formulaValidator⟩ : Packed) (by simp [items])
 obtain ⟨ltag,hl⟩ := h (⟨1,LiteralSyntaxValidator.lineValidator⟩ : Packed) (by simp [items])
 obtain ⟨btag,hb⟩ := h (⟨1,RawEqualityInstantiationAcceptance.logicalLeaf a b old⟩ : Packed) (by simp [items])
 obtain ⟨dtag,hd⟩ := h (⟨4,dispatcher a b old arithmetic x⟩ : Packed) (by simp [items])
 exact ⟨{
  qtag := qtag
  hq := hq
  ptag := ptag
  hp := hp
  ctag := ctag
  hc := hc
  atag := atag
  ha := ha
  vtag := vtag
  hv := hv
  ftag := ftag
  hf := hf
  ltag := ltag
  hl := hl
  btag := btag
  hb := hb
  dtag := dtag
  hd := hd
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawEqualityInstantiationDispatcher
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawEqualityInstantiationDispatcher
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawEqualityInstantiationCertificate
open GorbowSyntax GorbowPRProgram GorbowPRRegistry SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationCertificate
theorem installed (a b : Term 1) (old arithmetic : Program 1) (x : Program 3) {n : Nat} (p : Program n)
 (h : ∀ q ∈ items a b old arithmetic x, ∃ tag : Nat, (nodes p)[tag]? = some q) :
 Nonempty (LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationCertificate.Installation p a b old arithmetic x) := by
 obtain ⟨parent⟩ := LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawEqualityInstantiationDispatcher.installed a b old arithmetic x p (fun q hq => h q (by simp only [items,List.mem_append]; exact Or.inl hq))
 obtain ⟨itag,hi⟩ := h (⟨4,SixSol20261112.HistoryMachine.iterator (kernel a b old arithmetic x)⟩ : Packed) (by simp [items])
 obtain ⟨qctag,hqc⟩ := h (⟨5,checker a b old arithmetic x⟩ : Packed) (by simp [items])
 obtain ⟨utag,hu⟩ := h (⟨5,verifier a b old arithmetic x⟩ : Packed) (by simp [items])
 exact ⟨{
  toInstallation := parent
  itag := itag
  hi := hi
  qctag := qctag
  hqc := hqc
  utag := utag
  hu := hu
 }⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawEqualityInstantiationCertificate
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.CumulativeInstantiationRegistry.Items_RawEqualityInstantiationCertificate
