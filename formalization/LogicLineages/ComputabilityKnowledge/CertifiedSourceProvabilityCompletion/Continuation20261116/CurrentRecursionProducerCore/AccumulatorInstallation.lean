module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AccumulatorInstallation
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open SixSol20261112.Fuel NamedArithmeticGraph

theorem installed {arity k m : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G) :
 ∃ A : CurrentRecursionAccumulator.Installation p (CurrentRecursionBaseProgram.program base B)
  (CurrentRecursionProducerProgram.formula base step) (CurrentRecursionProducerProgram.step base step G),
 A.producerTag = R.producer.accumulatorTag ∧ A.baseTag = R.producer.baseTag := by
 obtain ⟨ftag,hf⟩ := R.hItems (⟨m+2,CurrentRecursionProducerProgram.formula base step⟩ : Packed)
  (by simp only [CurrentRecursionProducerSource.producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 obtain ⟨stag,hs⟩ := R.hItems (⟨m+2,CurrentRecursionProducerProgram.step base step G⟩ : Packed)
  (by simp only [CurrentRecursionProducerSource.producerItems,List.mem_cons,List.not_mem_nil,or_false]; tauto)
 exact ⟨{
   producerTag := R.producer.accumulatorTag,baseTag := R.producer.baseTag,formulaTag := ftag,stepTag := stag,
   h_producer := R.producer.haccumulator,h_base := R.producer.hbase,h_formula := hf,h_step := hs},rfl,rfl⟩

theorem formulaGraph {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (A : CurrentRecursionAccumulator.Installation p (CurrentRecursionBaseProgram.program base B)
  (CurrentRecursionProducerProgram.formula base step) (CurrentRecursionProducerProgram.step base step G))
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionAccumulator.familyCall A.formulaTag counter (Term.numeral R.qTag ::ᵥ inputs))
   (formulaCall R.producer.formulaTag R.qTag counter inputs))) :=
 CurrentRecursionProducerProgram.SwapGraph.swapCall p _ R.producer.formulaTag R.producer.hformula
  counter (Term.numeral R.qTag) inputs A.formulaTag A.h_formula

theorem stepGraph {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (A : CurrentRecursionAccumulator.Installation p (CurrentRecursionBaseProgram.program base B)
  (CurrentRecursionProducerProgram.formula base step) (CurrentRecursionProducerProgram.step base step G))
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (CurrentRecursionAccumulator.familyCall A.stepTag counter (Term.numeral R.qTag ::ᵥ inputs))
   (producerCall R.producer.stepTag R.qTag counter inputs))) :=
 CurrentRecursionProducerProgram.SwapGraph.swapCall p _ R.producer.stepTag R.producer.hstep
  counter (Term.numeral R.qTag) inputs A.stepTag A.h_step

theorem publicGraph {arity k m ctx : Nat} (p : Program arity) (installed : Formula 1) (lhs rhs : Term 1) (t : Term k)
 (old a : Program 1) (baseX : Program 3) (base : Program m) (step : Program (m+2)) (B : Program (m+1)) (G : Program (m+3))
 (R : CurrentRecursionProducerSource.Installation p installed lhs rhs t old a baseX base step B G)
 (A : CurrentRecursionAccumulator.Installation p (CurrentRecursionBaseProgram.program base B)
  (CurrentRecursionProducerProgram.formula base step) (CurrentRecursionProducerProgram.step base step G))
 (counter : Term ctx) (inputs : List.Vector (Term ctx) m) :
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (producerCall R.producer.publicTag R.qTag counter inputs)
   (CurrentRecursionAccumulator.familyCall A.producerTag counter (Term.numeral R.qTag ::ᵥ inputs)))) :=
 CurrentRecursionProducerProgram.SwapGraph.swapCall p _ A.producerTag A.h_producer
  (Term.numeral R.qTag) counter inputs R.producer.publicTag R.producer.hpublic
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AccumulatorInstallation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionProducerCore.AccumulatorInstallation
