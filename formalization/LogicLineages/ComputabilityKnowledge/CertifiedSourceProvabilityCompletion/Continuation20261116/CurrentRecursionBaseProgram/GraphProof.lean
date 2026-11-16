module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.SeedGraphProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.TransitivityGraphProof
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.CallGraphProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem exactInternal : Targets.InternalBase := by
 intro arity p m base child J tag I ht ctx target inputs
 let args := target ::ᵥ inputs
 let K := CurrentCalculationFormulaProgram.codecTags J.ctag J.atag J.ntag
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.ntag)
 have hparent : Computes p (parentCode m) args
  (callValue K target (LiteralNumeralPrefix.numeralCall J.ntag .zero ::ᵥ nums)) := by
  intro ptag hp
  obtain ⟨hg⟩ := GraphInputs.termQuoteGraph p args _ _ (rawValues J target inputs) J.ctag J.atag I.hc I.ha
   (GraphInputs.rootArgs p J I.hn target inputs) ptag hp
  obtain ⟨hv⟩ := CallGraphProof.parentValue p J I.hc I.ha I.hn target inputs
  exact ⟨Logic.trans _ _ _ hg hv⟩
 have hchild : Computes p (childCode m) args (callValue K (.succ target) nums) := by
  intro ctag hc
  obtain ⟨hg⟩ := GraphInputs.termQuoteGraph p args _ _ (rawValues J target inputs) J.ctag J.atag I.hc I.ha
   (GraphInputs.rootArgs p J I.hn target inputs) ctag hc
  obtain ⟨hv⟩ := CallGraphProof.childValue p J I.hc I.ha I.hn target inputs
  exact ⟨Logic.trans _ _ _ hg hv⟩
 have hresult := unary p args LiteralNumeralPrefix.numeralCode J.ntag I.hn
  (CurrentCalculationFormulaProgram.tailProgram base) (call J.baseTag inputs)
  (CurrentCalculationFormulaProgram.GraphProof.tailCall p base J.baseTag I.hb target inputs)
 have hseed := SeedGraphProof.seedGraph p args base child J I m (rootTemplate m) (rootArguments m)
  (rawValues J target inputs) (GraphInputs.rootArgs p J I.hn target inputs)
 have hchildCert := GraphInputs.childCall p child J.childTag I.hchild target inputs
 exact TransitivityGraphProof.transitivityGraph p args base child J I _ _ _ _ _ _ _ _ _ _
  hparent hchild hresult hseed hchildCert tag ht
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.GraphProof
