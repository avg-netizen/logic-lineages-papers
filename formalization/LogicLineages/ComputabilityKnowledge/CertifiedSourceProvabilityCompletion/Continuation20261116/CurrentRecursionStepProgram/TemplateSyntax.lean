module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open CurrentRecursionBaseProgram.NativePrimitives CurrentRecursionBaseProgram.TransitivityNativeProof
open HistoryRuleSuffix.NativeProof PrescribedRuntimeEquality CurrentImplicationCertificate CurrentEqualityImplication
open GorbowSubstitution GorbowFormulaSubstitution GorbowRegistryTuple

theorem shiftSubstitute {a b : Nat} (sigma : Fin a → Term b) (offset : Nat) (t : Term a) :
 substitute sigma (shiftTerm offset t) = shiftTerm offset (substitute sigma t) := by
 induction offset with
 | zero => rfl
 | succ n ih =>
  change Term.succ (substitute sigma (shiftTerm n t)) = Term.succ (shiftTerm n (substitute sigma t))
  rw [ih]
theorem shiftNumeral (offset target : Nat) (ctx : Nat) :
 shiftTerm offset (Term.numeral (n := ctx) target) = Term.numeral (target+offset) := by
 induction offset with
 | zero => rfl
 | succ n ih =>
  change Term.succ (shiftTerm n (Term.numeral (n := ctx) target)) = Term.numeral (target+(n+1))
  rw [ih]
  rfl

theorem openCallSubstitute {a b m : Nat} (sigma : Fin a → Term b) (target : Term a) (xs : List.Vector (Term a) m) :
 substitute sigma (CurrentRecursionBaseProgram.openCall target xs) =
 CurrentRecursionBaseProgram.openCall (substitute sigma target) (xs.map (substitute sigma)) := by
 simp only [CurrentRecursionBaseProgram.openCall,substitute,CurrentCalculationFormulaProgram.NativeProof.substPair,
  CurrentCalculationFormulaProgram.NativeProof.substTuple,SixSol20261112.Fuel.Logic.substNumeral,List.Vector.toList_map]

theorem paramsPlug (m target : Nat) :
 (params m).map (substitute (CurrentRecursionBaseProgram.TagSyntax.plug (m+1) target)) = tailVariables m := by
 ext i
 simp only [params,List.Vector.get_map,List.Vector.get_ofFn,substitute,CurrentRecursionBaseProgram.TagSyntax.plugCast,tailVariables]

theorem priorPlug (m target : Nat) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.plug (m+1) target) (priorTemplate m) =
 call target (.var 0 ::ᵥ tailVariables m) := by
 simp only [priorTemplate,openCallSubstitute,substitute,CurrentRecursionBaseProgram.TagSyntax.plugLast,
  List.Vector.map_cons,paramsPlug]
 rfl

theorem nextPlug (m target : Nat) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.plug (m+1) target) (nextTemplate m) =
 call target (.succ (.var 0) ::ᵥ tailVariables m) := by
 simp only [nextTemplate,openCallSubstitute,substitute,CurrentRecursionBaseProgram.TagSyntax.plugLast,
  List.Vector.map_cons,paramsPlug]
 rfl

theorem leftPlug (m offset target : Nat) :
 substitute (CurrentRecursionBaseProgram.TagSyntax.plug (m+1) target) (leftTemplate m offset) =
 call (target+offset) (.var 0 ::ᵥ call target (.var 0 ::ᵥ tailVariables m) ::ᵥ tailVariables m) := by
 simp only [leftTemplate,openCallSubstitute,shiftSubstitute,substitute,CurrentRecursionBaseProgram.TagSyntax.plugLast,
  shiftNumeral,List.Vector.map_cons,priorPlug,paramsPlug]
 rfl

theorem rootPlug {m : Nat} (base : Program m) (target : Nat) :
 substituteFormula (CurrentRecursionBaseProgram.TagSyntax.plug (m+1) target) (rootTemplate m (GorbowPRChildTags.stepTag base)) =
 CurrentRecursionStepCertificate.rootFormula base target := by
 simp only [rootTemplate,substituteFormula,nextPlug,leftPlug,CurrentRecursionStepCertificate.rootFormula]
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentRecursionStepProgram.TemplateSyntax
