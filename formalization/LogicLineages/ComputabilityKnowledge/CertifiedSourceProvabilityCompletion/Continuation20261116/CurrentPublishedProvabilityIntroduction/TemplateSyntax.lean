module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.SyntaxSupport
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateSyntax
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof GorbowPublishedDCB SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
open GorbowSubstitution GorbowFormulaSubstitution FixedFormulaSubstitution SyntaxSupport

theorem inner (v : List.Vector Nat 7) (u : Term 0) :
 substituteFormula (assignment innerEnvironment (NativeInputs.innerTerms v u)) bodyTemplate =
 checkerInner (v.get 0) (v.get 1) (v.get 2) u := by
 simp only [bodyTemplate,substituteFormula,CurrentRecursionStepProgram.TemplateSyntax.openCallSubstitute,
  substitute,List.Vector.map_cons,List.Vector.map_nil,assignment,innerEnvironment,NativeInputs.innerTerms,
  Fin.cases_zero,Fin.cases_succ]
 change Formula.equal (CurrentRecursionBaseProgram.openCall (closed (Term.numeral (v.get 0)))
  (closed (Term.numeral (v.get 1)) ::ᵥ closed (Term.numeral (v.get 2)) ::ᵥ .zero ::ᵥ closed u ::ᵥ .var 0 ::ᵥ nil)) (.succ .zero) = _
 rw [closedNumeral,closedNumeral,closedNumeral]
 rfl

theorem outer (v : List.Vector Nat 7) (u : Term 0) :
 substituteFormula (assignment outerEnvironment (NativeInputs.outerTerms v u)) (.ex bodyTemplate) =
 Formula.ex (checkerBody (v.get 0) (v.get 1) u) := by
 simp only [bodyTemplate,substituteFormula,CurrentRecursionStepProgram.TemplateSyntax.openCallSubstitute,
  substitute,List.Vector.map_cons,List.Vector.map_nil,liftSubstitute,assignment,outerEnvironment,NativeInputs.outerTerms,
  Fin.cases_zero,Fin.cases_succ]
 change Formula.ex (Formula.equal (CurrentRecursionBaseProgram.openCall (renameTerm Fin.succ (closed (n := 1) (Term.numeral (v.get 0))))
  (renameTerm Fin.succ (closed (n := 1) (Term.numeral (v.get 1))) ::ᵥ .var 1 ::ᵥ .zero ::ᵥ
   renameTerm Fin.succ (closed (n := 1) u) ::ᵥ .var 0 ::ᵥ nil)) (.succ .zero)) = _
 rw [renameClosed,renameClosed,renameClosed,closedNumeral,closedNumeral]
 rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateSyntax
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateSyntax
