module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.Preflight
public import LogicLineages.ComputabilityKnowledge.GorbowPRInternalCoherenceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof
/-- Actual node occurrence supplies the literal original defining axiom. -/
theorem member {arity m n : Nat} (p : Program arity) (f : Program n)
 (g : Fin n → Program m) (tag : Nat)
 (h : (nodes p)[tag]? = some ⟨m,Program.composition f g⟩) :
 GorbowStandardInduction.universalClosure (rootFormula f g tag) ∈ axioms p := by
 apply EffectiveNumeral.NodeSupport.intoRegistry (.composition f g) arity p tag h
 apply EffectiveNumeral.NodeSupport.rootIncluded
 exact List.mem_singleton.mpr rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionCertificate.RootProof
