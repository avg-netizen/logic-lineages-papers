module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix

/-- Literal original number, every runtime tag, all child numeric outputs. -/
def NativeBase : Prop := ∀ m (base : Program m) (child : Program (m+1)) target (inputs : List.Vector Nat m),
 evaluate (program base child) (target ::ᵥ inputs) =
 CurrentRecursionBaseCertificate.number target inputs (evaluate base inputs) (evaluate child ((target+1) ::ᵥ inputs))
/-- Arbitrary symbolic actual child call, exact zero-root specialization and
original transitivity. No child success/CORE/calibration premise; no new source
existence is asserted by these explicit membership preconditions. -/
def InternalBase : Prop := ∀ arity (p : Program arity) m (base : Program m) (child : Program (m+1))
 (J : Tags) (tag : Nat), Installation p base child J →
 (nodes p)[tag]? = some ⟨m+1,program base child⟩ →
 ∀ ctx (target : Term ctx) (inputs : List.Vector (Term ctx) m),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call tag (target ::ᵥ inputs)) (value J target inputs)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionBaseProgram.Targets
