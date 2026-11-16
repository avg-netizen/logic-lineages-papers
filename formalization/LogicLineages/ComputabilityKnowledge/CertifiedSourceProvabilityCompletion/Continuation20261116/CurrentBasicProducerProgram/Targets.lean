module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence

/-- Every runtime tag and numeric input, exact literal original leaf recipe. -/
def NativeLeaf : Prop := ∀ n (kind : Kind n) target (inputs : List.Vector Nat n),
 evaluate (program kind) (target ::ᵥ inputs) = number kind target inputs

/-- Actual arbitrary-symbolic producer graph. No evaluator calibration,
certificate-validity or CORE premise; primitive and producer memberships only. -/
def InternalLeaf : Prop := ∀ arity (p : Program arity) n (kind : Kind n) (J : Tags) (producerTag : Nat),
 Installation p J → (nodes p)[producerTag]? = some ⟨n+1,program kind⟩ →
 ∀ ctx (target : Term ctx) (inputs : List.Vector (Term ctx) n),
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (call producerTag (target ::ᵥ inputs)) (value kind J target inputs)))

/-- Same actual source/root/index/fuel, with fixed-I seed bound before kind,
node, producer and runtime choices. The only extra premise is the original fuel
guard. Defining axiom membership must be derived from the actual basic node.
No child IH is needed and no whole-inventory/source existence is claimed. -/
def SourceCore : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ n (kind : Kind n) (J : Tags) (target producerTag : Nat),
 Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) J →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? = some ⟨n,evaluator kind⟩ →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? = some ⟨n+1,program kind⟩ →
 ∀ ctx (assumptions : List (Formula ctx)) (inputs : List.Vector (Term ctx) n) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local U ctx assumptions (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel
   (CurrentRecursionProducerCore.childFormula (PrescribedRuntimeCallCongruence.tags I.previous) target inputs)
   (call producerTag (Term.numeral target ::ᵥ inputs))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentBasicProducerProgram.Targets
