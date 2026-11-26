module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.Preflight
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SyntaxProof
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRChildTags GorbowPRDefiningEquations GorbowTheoryProof SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowRegistryTuple PrescribedRuntimeEquality PrescribedRuntimeCallCongruence HistoryRuleSuffix
open GorbowSubstitution GorbowFormulaSubstitution
open CurrentRecursionBaseProgram.TagSyntax CurrentRecursionStepProgram.TemplateSyntax

theorem arguments (m target : Nat) :
 (List.Vector.ofFn (fun i : Fin m => (Term.var i.castSucc : Term (m+1)))).map
  (substitute (plug m target)) = argumentVariables m := by
 ext i
 simp only [List.Vector.get_map,List.Vector.get_ofFn,substitute,plugCast,argumentVariables]

theorem children {m n : Nat} (f : Program n) (g : Fin n → Program m) (target : Nat) :
 (List.Vector.ofFn (fun i => CurrentRecursionBaseProgram.openCall
  (CurrentRecursionStepProgram.shiftTerm (argumentTag f g i) (.var (Fin.last m)))
  (List.Vector.ofFn (fun j : Fin m => (Term.var j.castSucc : Term (m+1)))))).map (substitute (plug m target)) =
 List.Vector.ofFn (fun i => call (target+argumentTag f g i) (argumentVariables m)) := by
 ext i
 simp only [List.Vector.get_map,List.Vector.get_ofFn,openCallSubstitute,shiftSubstitute,substitute,plugLast,arguments,shiftNumeral]
 rfl

theorem root {m n : Nat} (f : Program n) (g : Fin n → Program m) (target : Nat) :
 substituteFormula (plug m target) (rootTemplate f g) = CurrentCompositionCertificate.rootFormula f g target := by
 simp only [rootTemplate,substituteFormula,openCallSubstitute,substitute,plugLast,arguments,children,
  CurrentCompositionCertificate.rootFormula]
 rfl

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SyntaxProof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentCompositionProducerProgram.SyntaxProof
