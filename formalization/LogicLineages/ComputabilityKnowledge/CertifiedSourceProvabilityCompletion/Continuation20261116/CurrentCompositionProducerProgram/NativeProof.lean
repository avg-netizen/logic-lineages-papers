module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeOperands
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SeedNative
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open HistoryRuleSuffix.NativeProof
open CurrentRecursionBaseProgram.TransitivityNativeProof

attribute [local irreducible] evaluate in
 theorem exactNative : Targets.NativeComposition := by
 intro m n f g F G target inputs
 let args := target ::ᵥ inputs
 let vals := List.Vector.ofFn (fun i => evaluate (g i) inputs)
 let nums := GorbowPRNumeralCalculation.numeralArguments inputs
 let leftTerms := List.Vector.ofFn (fun i => call (target+argumentTag f g i) nums)
 let rightTerms := GorbowPRNumeralCalculation.numeralArguments vals
 let codes := List.Vector.ofFn (fun i => evaluate (G i) ((target+argumentTag f g i) ::ᵥ inputs))
 let tagProg : Program (m+1) := .projection 0
 let nextProg := applyOne .succ tagProg
 let parentProg := callCode tagProg (rawPrograms m)
 let leftProg := callCode nextProg (argumentCalls f g)
 let rightProg := callCode nextProg ((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode))
 let outputProg := applyOne LiteralNumeralPrefix.numeralCode (Program.composition f (argumentValues g).get)
 let seedProg := CurrentRecursionBaseProgram.seedProgram m (rootTemplate f g) (CurrentRecursionBaseProgram.rootArguments m)
 let congrProg := CurrentCallCongruenceProgram.callConstructor nextProg (argumentCalls f g)
  ((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)) (argumentCodes f g G)
 let functionProg := Program.composition F (Fin.cases nextProg (argumentValues g).get)
 have htag : evaluate tagProg args = target := projectionEval _ _
 have hnext : evaluate nextProg args = target+1 := by
  have h := CurrentRecursionStepProgram.NativeEvaluation.shiftEval 1 tagProg args
  rw [htag] at h
  exact h
 have hnums : ∀ i, evaluate ((rawPrograms m).get i) args = Encodable.encode (GorbowTermPrefixCode.encode (nums.get i)) := by
  intro i
  simpa only [nums,GorbowPRNumeralCalculation.numeralArguments,List.Vector.get_map] using NativeValues.rawEval target inputs i
 have hlefts : ∀ i, evaluate ((argumentCalls f g).get i) args = Encodable.encode (GorbowTermPrefixCode.encode (leftTerms.get i)) := by
  intro i
  simpa only [leftTerms,List.Vector.get_ofFn] using NativeOperands.quotedArgument f g target inputs i
 have hrights : ∀ i, evaluate (((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)).get i) args =
  Encodable.encode (GorbowTermPrefixCode.encode (rightTerms.get i)) := by
  intro i
  simpa only [rightTerms,GorbowPRNumeralCalculation.numeralArguments,List.Vector.get_map,vals,List.Vector.get_ofFn] using NativeOperands.rawValue g target inputs i
 have hcodes : ∀ i, evaluate ((argumentCodes f g G).get i) args = codes.get i := by
  intro i
  simpa only [codes,List.Vector.get_ofFn] using NativeValues.childEval f g G target inputs i
 have hparent := CallEncoding.native tagProg (rawPrograms m) args target nums htag hnums
 have hleft := CallEncoding.native nextProg (argumentCalls f g) args (target+1) leftTerms hnext hlefts
 have hright := CallEncoding.native nextProg ((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)) args (target+1) rightTerms hnext hrights
 have houtput : evaluate outputProg args = Encodable.encode (GorbowTermPrefixCode.encode (Term.numeral (evaluate f vals) : Term 0)) := by
  change evaluate (applyOne LiteralNumeralPrefix.numeralCode (.composition f (argumentValues g).get)) args = _
  rw [oneEval,NativeOperands.result,LiteralNumeralPrefix.StatementChecks.exactNative]
 have hseed := SeedNative.seed f g target inputs
 have hcongr := CurrentCallCongruenceProgram.NativeCall.certificate nextProg (argumentCalls f g)
  ((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)) (argumentCodes f g G) args (target+1) leftTerms rightTerms codes hnext hlefts hrights hcodes
 have hfunction := NativeOperands.functionCode g F target inputs
 have hinner := transitivityEval parentProg leftProg rightProg seedProg congrProg args
  (call target nums) (call (target+1) leftTerms) (call (target+1) rightTerms) hparent hleft hright
 have houter := transitivityEval parentProg rightProg outputProg
  (CurrentRecursionBaseProgram.transitivity parentProg leftProg rightProg seedProg congrProg) functionProg args
  (call target nums) (call (target+1) rightTerms) (Term.numeral (evaluate f vals)) hparent hright houtput
 change evaluate (CurrentRecursionBaseProgram.transitivity parentProg rightProg outputProg
  (CurrentRecursionBaseProgram.transitivity parentProg leftProg rightProg seedProg congrProg) functionProg) args = _
 rw [houter,hinner]
 change transitivityNumber (call target nums) (call (target+1) rightTerms) (Term.numeral (evaluate f vals))
  (transitivityNumber (call target nums) (call (target+1) leftTerms) (call (target+1) rightTerms)
   (evaluate (CurrentRecursionBaseProgram.seedProgram m (rootTemplate f g) (CurrentRecursionBaseProgram.rootArguments m)) args)
   (evaluate (CurrentCallCongruenceProgram.callConstructor nextProg (argumentCalls f g)
    ((argumentValues g).map (applyOne LiteralNumeralPrefix.numeralCode)) (argumentCodes f g G)) args))
  (evaluate (.composition F (Fin.cases nextProg (argumentValues g).get)) args) = _
 rw [hseed,hcongr,hfunction]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.NativeProof
