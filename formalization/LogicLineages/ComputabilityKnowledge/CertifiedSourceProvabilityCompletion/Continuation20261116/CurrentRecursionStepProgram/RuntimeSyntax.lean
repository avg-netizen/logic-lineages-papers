module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.RuntimeSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open GorbowSubstitution GorbowFormulaSubstitution GorbowRegistryTuple TemplateSyntax

theorem tailPlug (m target : Nat) :
 (List.Vector.ofFn (fun i : Fin m => (Term.var i.succ.succ.castSucc : Term (m+3)))).map
  (substitute (CurrentRecursionBaseProgram.TagSyntax.plug (m+2) target)) =
 List.Vector.ofFn (fun i : Fin m => (Term.var i.succ.succ : Term (m+2))) := by
 ext i
 simp only [List.Vector.get_map,List.Vector.get_ofFn,substitute,CurrentRecursionBaseProgram.TagSyntax.plugCast]

theorem rightPlug (m offset target : Nat) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.plug (m+2) target) (rightTemplate m offset) =
 call (target+offset) (.var 0 ::ᵥ .var 1 ::ᵥ List.Vector.ofFn (fun i : Fin m => (.var i.succ.succ : Term (m+2)))) := by
 simp only [rightTemplate,openCallSubstitute,shiftSubstitute,substitute,CurrentRecursionBaseProgram.TagSyntax.plugLast,
  shiftNumeral,List.Vector.map_cons,tailPlug]
 all_goals rfl

theorem unaryPlug (m offset target : Nat) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.plug (m+2) target) (unaryTemplate m offset) =
 CurrentRecursionStepCertificate.stepTemplate m (target+offset) := by
 simp only [unaryTemplate,openCallSubstitute,shiftSubstitute,substitute,CurrentRecursionBaseProgram.TagSyntax.plugLast,
  shiftNumeral,List.Vector.map_cons,tailPlug,CurrentRecursionStepCertificate.stepTemplate]
 all_goals rfl

theorem full {n : Nat} (target : Nat) (t : Term (n+1)) (sigma : Fin n → Term 0) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.join target sigma) t =
 substitute sigma (substitute (CurrentRecursionBaseProgram.TagSyntax.plug n target) t) := by
 rw [GorbowSubstitution.substitute_composition,CurrentRecursionBaseProgram.TagSyntax.full]

theorem head {n : Nat} (target : Nat) (t : Term (n+2)) (sigma : Fin n → Term 0) :
 substitute (liftSubstitute (CurrentRecursionBaseProgram.TagSyntax.join target sigma)) t =
 substitute (liftSubstitute sigma) (substitute (CurrentRecursionBaseProgram.TagSyntax.plug (n+1) target) t) := by
 rw [GorbowSubstitution.substitute_composition]
 change _ = substitute (fun i => substitute (liftSubstitute sigma) (liftSubstitute (CurrentRecursionBaseProgram.TagSyntax.plug n target) i)) t
 rw [GorbowFormulaCompositionProof.liftComposition,CurrentRecursionBaseProgram.TagSyntax.full]

theorem tailNumerals {m : Nat} (counter : Nat) (inputs : List.Vector Nat m) :
 (tailVariables m).map (substitute (fun i => (Term.numeral ((counter ::ᵥ inputs).get i) : Term 0))) =
 GorbowPRNumeralCalculation.numeralArguments inputs := by
 ext i
 simp only [tailVariables,List.Vector.get_map,List.Vector.get_ofFn,substitute,List.Vector.get_cons_succ,
  GorbowPRNumeralCalculation.numeralArguments]

theorem tailTwoNumerals {m : Nat} (counter previous : Nat) (inputs : List.Vector Nat m) :
 (List.Vector.ofFn (fun i : Fin m => (Term.var i.succ.succ : Term (m+2)))).map
  (substitute (fun i => (Term.numeral ((counter ::ᵥ previous ::ᵥ inputs).get i) : Term 0))) =
 GorbowPRNumeralCalculation.numeralArguments inputs := by
 ext i
 simp only [List.Vector.get_map,List.Vector.get_ofFn,substitute,List.Vector.get_cons_succ,GorbowPRNumeralCalculation.numeralArguments]

theorem priorClosed (m target counter : Nat) (inputs : List.Vector Nat m) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.join target (fun i => Term.numeral ((counter ::ᵥ inputs).get i))) (priorTemplate m) =
 call target (Term.numeral counter ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs) := by
 rw [full,priorPlug]
 simp only [SixSol20261112.Fuel.Logic.substCall,List.Vector.map_cons,substitute,List.Vector.get_cons_zero,tailNumerals]

theorem nextClosed (m target counter : Nat) (inputs : List.Vector Nat m) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.join target (fun i => Term.numeral ((counter ::ᵥ inputs).get i))) (nextTemplate m) =
 call target (Term.numeral (counter+1) ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs) := by
 rw [full,nextPlug]
 simp only [SixSol20261112.Fuel.Logic.substCall,List.Vector.map_cons,substitute,List.Vector.get_cons_zero,tailNumerals]
 all_goals rfl

theorem leftClosed (m offset target counter : Nat) (inputs : List.Vector Nat m) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.join target (fun i => Term.numeral ((counter ::ᵥ inputs).get i))) (leftTemplate m offset) =
 call (target+offset) (Term.numeral counter ::ᵥ call target (Term.numeral counter ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs) ::ᵥ
  GorbowPRNumeralCalculation.numeralArguments inputs) := by
 rw [full,leftPlug]
 simp only [SixSol20261112.Fuel.Logic.substCall,List.Vector.map_cons,substitute,List.Vector.get_cons_zero,tailNumerals]

theorem rightClosed (m offset target counter previous : Nat) (inputs : List.Vector Nat m) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.join target (fun i => Term.numeral ((counter ::ᵥ previous ::ᵥ inputs).get i))) (rightTemplate m offset) =
 call (target+offset) (Term.numeral counter ::ᵥ Term.numeral previous ::ᵥ GorbowPRNumeralCalculation.numeralArguments inputs) := by
 rw [full,rightPlug]
 simp only [SixSol20261112.Fuel.Logic.substCall,List.Vector.map_cons,substitute,List.Vector.get_cons_zero,tailTwoNumerals]
 all_goals rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.RuntimeSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.RuntimeSyntax
