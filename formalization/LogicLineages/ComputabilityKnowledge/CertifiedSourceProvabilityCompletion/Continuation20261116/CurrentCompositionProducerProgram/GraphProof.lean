module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.GraphOperands
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SeedGraph
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.GraphProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open SixSol20261112.Fuel NamedArithmeticGraph LiteralRawMP.ConstructorSupportProof

theorem exactInternal : Targets.InternalComposition := by
 intro arity p m n f g F G J producerTag I hp ctx target inputs
 let args := target ::ᵥ inputs
 let values : List.Vector (Term ctx) n := List.Vector.ofFn (fun i => call (J.argumentTags i) inputs)
 let codes : List.Vector (Term ctx) n := List.Vector.ofFn (fun i => call (J.argumentProducerTags i)
  (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target ::ᵥ inputs))
 let nums := inputs.map (LiteralNumeralPrefix.numeralCall J.C.numeralTag)
 let leftArgs := List.Vector.ofFn (fun i => callValue J.C (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) target) nums)
 let rightArgs := values.map (LiteralNumeralPrefix.numeralCall J.C.numeralTag)
 have htarget : Computes p (Program.projection (0 : Fin (m+1))) args target := projection p args 0
 have hnext := CurrentRecursionStepProgram.EvaluatorGraph.successorGraph p args (.projection 0) target htarget
 have hnums : ∀ i, Computes p ((rawPrograms m).get i) args (nums.get i) := by
  intro i
  simpa only [nums,List.Vector.get_map] using GraphOperands.raw p f g F G J I target inputs i
 have hvalues : ∀ i, Computes p ((argumentValues g).get i) args (values.get i) := by
  intro i
  simpa only [values,List.Vector.get_ofFn] using GraphOperands.actualArgument p f g F G J I target inputs i
 have hcodes : ∀ i, Computes p ((argumentCodes f g G).get i) args (codes.get i) := by
  intro i
  simpa only [codes,List.Vector.get_ofFn] using GraphOperands.actualChild p f g F G J I target inputs i
 have hlefts : ∀ i, Computes p ((argumentCalls f g).get i) args (leftArgs.get i) := by
  intro i
  simpa only [leftArgs,List.Vector.get_ofFn] using GraphOperands.quotedArgument p f g F G J I target inputs i
 have hrights : ∀ i, Computes p (((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)).get i) args (rightArgs.get i) := by
  intro i
  have h := unary p args LiteralNumeralPrefix.numeralCode J.C.numeralTag I.primitives.hn _ _ (hvalues i)
  simp only [rightArgs,List.Vector.get_map,LiteralNumeralPrefix.numeralCall]
  exact h
 have hresult := CurrentRecursionAccumulator.GraphSupport.composition p args f J.functionTag I.hf (argumentValues g).get values hvalues
 have houtput := unary p args LiteralNumeralPrefix.numeralCode J.C.numeralTag I.primitives.hn _ _ hresult
 have hfunction : Computes p (.composition F (Fin.cases (applyOne .succ (.projection 0)) (argumentValues g).get)) args
  (call J.functionProducerTag (.succ target ::ᵥ values)) := by
  apply CurrentRecursionAccumulator.GraphSupport.composition p args F J.functionProducerTag I.hF _ (.succ target ::ᵥ values)
  intro i
  cases i using Fin.cases with
  | zero => exact hnext
  | succ i => exact hvalues i
 have hparent := CallEncoding.graph p args J.C I.primitives (.projection 0) (rawPrograms m) target nums htarget hnums
 have hleft := CallEncoding.graph p args J.C I.primitives (applyOne .succ (.projection 0)) (argumentCalls f g) (.succ target) leftArgs hnext hlefts
 have hright := CallEncoding.graph p args J.C I.primitives (applyOne .succ (.projection 0))
  ((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)) (.succ target) rightArgs hnext hrights
 have hsNodes : SeedGraph.SeedNodes p (seedTags J) :=
  ⟨I.hp,I.primitives.hc,I.primitives.ha,I.primitives.hm,I.h13⟩
 have hseed := SeedGraph.seedGraph p args (seedTags J) hsNodes m (rootTemplate f g)
  (CurrentRecursionBaseProgram.rootArguments m) (CurrentRecursionBaseProgram.rawValues (seedTags J) target inputs)
  (CurrentRecursionBaseProgram.GraphInputs.rootArgs p (seedTags J) I.primitives.hn target inputs)
 have hcongruence := CurrentCallCongruenceProgram.CallGraph.constructor p args J.C I.primitives (applyOne .succ (.projection 0)) (.succ target)
  (argumentCalls f g) ((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)) (argumentCodes f g G)
  leftArgs rightArgs codes hnext hlefts hrights hcodes
 have hfirst := CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph p args J.C I.primitives
  _ _ _ _ _ _ _ _ _ _ hparent hleft hright hseed hcongruence
 exact CurrentCallCongruenceProgram.TransitivityGraph.transitivityGraph p args J.C I.primitives
  _ _ _ _ _ _ _ _ _ _ hparent hright houtput hfirst hfunction producerTag hp

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.GraphProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.GraphProof
