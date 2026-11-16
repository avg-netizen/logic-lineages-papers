module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.Targets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundInterfaces
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence SixSol20261112.Fuel NamedArithmeticGraph
open CurrentRecursionProducerCore

/-- Proof interface: unchanged accepted constructor endpoint after its fixed bound. -/
def Leaf (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) (bound : Nat) : Prop :=
 ∀ n (kind : CurrentBasicProducerProgram.Kind n) (J : CurrentBasicProducerProgram.Tags) (target producerTag : Nat),
 CurrentBasicProducerProgram.Installation (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) J →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? = some ⟨n,CurrentBasicProducerProgram.evaluator kind⟩ →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? = some ⟨n+1,CurrentBasicProducerProgram.program kind⟩ →
 ∀ ctx (assumptions : List (Formula ctx)) (inputs : List.Vector (Term ctx) n) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local U ctx assumptions (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel
   (CurrentRecursionProducerCore.childFormula (PrescribedRuntimeCallCongruence.tags I.previous) target inputs)
   (call producerTag (Term.numeral target ::ᵥ inputs))))


/-- Proof interface: unchanged accepted constructor endpoint after its fixed bound. -/
def Composition (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) (bound : Nat) : Prop :=
 ∀ m n (f : Program n) (g : Fin n → Program m)
 (F : Program (n+1)) (G : Fin n → Program (m+1)) (J : CurrentCompositionProducerProgram.Tags n)
 (target producerTag : Nat),
 CurrentCompositionProducerProgram.Installation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX) f g F G J →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[target]? =
  some ⟨m,Program.composition f g⟩ →
 (nodes (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX))[producerTag]? =
  some ⟨m+1,CurrentCompositionProducerProgram.program f g F G⟩ →
 ∀ ctx (assumptions : List (Formula ctx)) (inputs : List.Vector (Term ctx) m) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let K := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let values := CurrentCompositionProducerCore.childValues f g target inputs
 Nonempty (Hilbert.Local U ctx assumptions (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 (∀ i, Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel (calculation K (target+argumentTag f g i) inputs)
   (CurrentCompositionProducerCore.producerCode (J.argumentProducerTags i) (target+argumentTag f g i) inputs)))) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel (calculation K (target+1) values)
   (CurrentCompositionProducerCore.producerCode J.functionProducerTag (target+1) values))) →
 Nonempty (Hilbert.Local U ctx assumptions
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (calculation K target inputs) (CurrentCompositionProducerCore.producerCode producerTag target inputs)))


/-- Proof interface: unchanged accepted constructor endpoint after its fixed bound. -/
def Recursion (installed : Formula 1) (lhs rhs : Term 1) {k : Nat} (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code)
 (I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX)) (bound : Nat) : Prop :=
 ∀ m (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3)),
 ∀ R : CurrentRecursionProducerSource.Installation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a baseX base step B G,
 ∀ ctx (inputs : List.Vector (Term ctx) m) (fuel counter : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let liftedInputs := inputs.map SixSol20261112.Fuel.liftTerm
 let childArgs := stepInputs R.qTag (.var 0 : Term (ctx+1)) liftedInputs
 let childTag := R.qTag+GorbowPRChildTags.stepTag base
 Nonempty (Derivation U (SixSol20261112.Fuel.orderGuard (Term.numeral bound) fuel)) →
 Nonempty (Derivation U
  (core I.currentK.coreTag index fuel (childFormula J (R.qTag+1) inputs) (childCode R.BTag (R.qTag+1) inputs))) →
 Nonempty (Derivation U
  (core I.currentK.coreTag (SixSol20261112.Fuel.liftTerm index) (SixSol20261112.Fuel.liftTerm fuel)
   (childFormula J childTag childArgs) (childCode R.GTag childTag childArgs))) →
 Nonempty (Derivation U
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (formulaCall R.producer.formulaTag R.qTag counter inputs)
   (producerCall R.producer.publicTag R.qTag counter inputs)))


end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundInterfaces
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentStructuralProducerCore.BoundInterfaces
