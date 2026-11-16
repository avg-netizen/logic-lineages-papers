module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeRules
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeQuotes
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeAssembly
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeInstances
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeSeed
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open NativeOperations NativeRules NativeQuotes

-- Keep evaluator recursion opaque during endpoint elaboration; all evaluation
-- steps below use previously checked calibration equations.
attribute [local irreducible] GorbowPRProgram.evaluate
attribute [local irreducible] liftNumber transitivityUnderNumber unaryRuleNumber PrescribedRuntimeSpecialization.produce

theorem exactNative : Targets.NativeStep := by
 intro m base step child target counter inputs
 dsimp only
 let v := target ::ᵥ counter ::ᵥ inputs
 let d := GorbowPRChildTags.stepTag base
 let av := GorbowPRNumeralCalculation.numeralArguments inputs
 let prev := evaluate (.recursion base step) (counter ::ᵥ inputs)
 let out := evaluate step (counter ::ᵥ prev ::ᵥ inputs)
 let pc := call target (Term.numeral counter ::ᵥ av)
 let pn := (Term.numeral prev : Term 0)
 let nc := call target (Term.numeral (counter+1) ::ᵥ av)
 let l := call (target+d) (Term.numeral counter ::ᵥ pc ::ᵥ av)
 let r := call (target+d) (Term.numeral counter ::ᵥ pn ::ᵥ av)
 let o := (Term.numeral out : Term 0)
 let raws := CurrentRecursionBaseProgram.rootArguments (m+1)
 let f := CurrentRecursionStepCertificate.closedStepFunction (target+d) counter inputs
 unfold program
 rw [NativeAssembly.assembled v _ _ _ _ _ _ _ _ _ pc pn nc l r o f
  (NativeLeaves.prior target counter inputs) (NativeLeaves.previousNumeral base step target counter inputs)
  (NativeLeaves.next target counter inputs) (NativeLeaves.left d target counter inputs)
  (rightQuote base step target counter inputs) (NativeLeaves.outputNumeral base step target counter inputs)
  (unaryQuote m d target counter inputs) (NativeInstances.leftInstance d target counter inputs)
  (NativeInstances.rightInstance base step target counter inputs)]
 rw [NativeSeed.seed,NativeEvaluation.childEval]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.NativeProof
