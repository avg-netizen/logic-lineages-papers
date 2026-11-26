module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
/-- Full actual AST evaluation equals the original explicit recipe with actual
child evaluations. Certificate outputs remain arbitrary; no validity assumed. -/
def NativeComposition : Prop := ∀ m n (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) target (inputs : List.Vector Nat m),
 evaluate (program f g F G) (target ::ᵥ inputs) = number f g F G target inputs
/-- Actual arbitrary-symbolic graph. All source requirements are concrete
memberships only; no result/calibration/child-correctness oracle is an input. -/
def InternalComposition : Prop := ∀ arity (p : Program arity) m n (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : Tags n) producerTag,
 Installation p f g F G J → (nodes p)[producerTag]? = some ⟨m+1,program f g F G⟩ →
 ∀ ctx (target : Term ctx) (inputs : List.Vector (Term ctx) m),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call producerTag (target ::ᵥ inputs)) (value f g J target inputs)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.Targets
