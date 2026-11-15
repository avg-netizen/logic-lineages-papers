module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorSequenceProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorTokenProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityProof
open GorbowTheoryProof SixSol20261113.HistoryCodec.ArithmeticSupport
/-- Uniform closure of all18 literal original term/formula constructor rows. -/
theorem constructorValidity : ConstructorValidityTargets.InternalConstructorValidity := by
 intro n p stag ptag ctag atag hs hp hc ha ctx G ctor bound children hchildren
 obtain ⟨hrow⟩ := ConstructorSequenceProof.sequence p G stag ctag atag hs hc ha _ children hchildren
 obtain ⟨htoken⟩ := ConstructorTokenProof.tokenScan p stag ptag ctag atag hs hp hc ha ctor bound
  (ConstructorValidityTargets.rawSequence atag children)
 exact ⟨localTrans _ _ _ (.base htoken) hrow⟩
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ConstructorValidityProof
