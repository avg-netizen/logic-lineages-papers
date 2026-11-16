module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix

/-- Same original literal successor number, actual evaluated child output.
No arbitrary previous acceptance/certificate input or success premise. -/
def NativeStep : Prop := ∀ m (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 target counter (inputs : List.Vector Nat m),
 let previous := evaluate (.recursion base step) (counter ::ᵥ inputs)
 let result := evaluate step (counter ::ᵥ previous ::ᵥ inputs)
 let childCode := evaluate child ((target + GorbowPRChildTags.stepTag base) ::ᵥ counter ::ᵥ previous ::ᵥ inputs)
 evaluate (program base step child) (target ::ᵥ counter ::ᵥ inputs) =
 CurrentRecursionStepCertificate.number base target counter inputs previous result childCode
/-- Actual AST graph with arbitrary symbolic target/counter/inputs, including
actual evaluator and child producer calls. Conditional memberships are NOT an
assertion that a new joint published source has been realized. -/
def InternalStep : Prop := ∀ arity (p : Program arity) m (base : Program m) (step : Program (m+2)) (child : Program (m+3))
 (J : Tags) (tag : Nat), Installation p base step child J →
 (nodes p)[tag]? = some ⟨m+2,program base step child⟩ →
 ∀ ctx (target counter : Term ctx) (inputs : List.Vector (Term ctx) m),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag (target ::ᵥ counter ::ᵥ inputs)) (value base J target counter inputs)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.Targets
