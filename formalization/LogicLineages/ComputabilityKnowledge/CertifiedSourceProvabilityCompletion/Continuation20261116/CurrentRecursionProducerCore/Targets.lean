module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open PrescribedRuntimeEquality PrescribedRuntimeCallCongruence
/-- Same new-root base constructor; original local child IH only. Fixed source
seed bound is chosen before program/node/runtime parameters. -/
def BaseCore : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ m (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3)),
 ∀ R : CurrentRecursionProducerSource.Installation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a baseX base step B G,
 ∀ ctx (assumptions : List (Formula ctx)) (inputs : List.Vector (Term ctx) m) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 Nonempty (Hilbert.Local U ctx assumptions (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel (childFormula J (R.qTag+1) inputs) (childCode R.BTag (R.qTag+1) inputs))) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel (formulaCall R.producer.formulaTag R.qTag .zero inputs)
   (call R.producer.baseTag (Term.numeral R.qTag ::ᵥ inputs))))

/-- Actual ordinary-step producer: no prior certificate or prior acceptance
premise. The step-child input previous value is the actual q(counter) call. -/
def StepCore : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ m (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3)),
 ∀ R : CurrentRecursionProducerSource.Installation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a baseX base step B G,
 ∀ ctx (assumptions : List (Formula ctx)) (counter : Term ctx) (inputs : List.Vector (Term ctx) m) (fuel : Term ctx),
 let U := S pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX)
 let J := tags I.previous
 let index : Term ctx := Term.numeral (Encodable.encode c)
 let childArgs := stepInputs R.qTag counter inputs
 let childTag := R.qTag+GorbowPRChildTags.stepTag base
 Nonempty (Hilbert.Local U ctx assumptions (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel (childFormula J childTag childArgs) (childCode R.GTag childTag childArgs))) →
 Nonempty (Hilbert.Local U ctx assumptions
  (core I.currentK.coreTag index fuel
   (impValue J.ctag J.atag (formulaCall R.producer.formulaTag R.qTag counter inputs)
    (formulaCall R.producer.formulaTag R.qTag (.succ counter) inputs))
   (producerCall R.producer.stepTag R.qTag counter inputs)))

/-- Fixed-source/index/fuel object-language induction for the actual public AST.
Only the base child and bound-variable step-child structural IH are assumptions.
The actual prior accumulator's acceptance is supplied by induction, never input. -/
def AccumulatorCore : Prop :=
 ∀ (installed : Formula 1) (lhs rhs : Term 1) k (t : Term k)
 (old a : Program 1) (baseX : Program 3) (pF pR : Program 1) (c : Code),
 Actual pF pR (CumulativePropositionalSource.verifier installed lhs rhs old a baseX) c →
 (∀ v, evaluate baseX v = HistoryDispatcher.axiomFunction v) →
 ∀ I : CumulativePropositionalSource.JointInstallation
  (CumulativePropositionalSource.root installed lhs rhs pF pR old a baseX)
  installed lhs rhs t old a (SaturatedAxiomLeaf.saturated baseX),
 ∃ seedFuel : Nat, ∀ m (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3)),
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
 Nonempty (Derivation U (SixSol20261112.Fuel.orderGuard (Term.numeral seedFuel) fuel)) →
 Nonempty (Derivation U
  (core I.currentK.coreTag index fuel (childFormula J (R.qTag+1) inputs) (childCode R.BTag (R.qTag+1) inputs))) →
 Nonempty (Derivation U
  (core I.currentK.coreTag (SixSol20261112.Fuel.liftTerm index) (SixSol20261112.Fuel.liftTerm fuel)
   (childFormula J childTag childArgs) (childCode R.GTag childTag childArgs))) →
 Nonempty (Derivation U
  (accepted I.currentK.coreTag I.currentK.verifierTag index fuel
   (formulaCall R.producer.formulaTag R.qTag counter inputs)
   (producerCall R.producer.publicTag R.qTag counter inputs)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.Targets
