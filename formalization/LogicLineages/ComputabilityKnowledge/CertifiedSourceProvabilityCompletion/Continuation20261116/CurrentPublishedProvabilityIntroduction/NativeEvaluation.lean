module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.TemplateSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeEvaluation
open GorbowSyntax GorbowPRProgram List.Vector
theorem composition {m n : Nat} (f : Program n) (g : Fin n → Program m) (v : List.Vector Nat m) :
 evaluate (.composition f g) v = evaluate f (List.Vector.ofFn (fun i => evaluate (g i) v)) := rfl

theorem three {n : Nat} (f : Program 3) (a b c : Program n) (v : List.Vector Nat n) :
 evaluate (.composition f (Fin.cases a (Fin.cases b (Fin.cases c Fin.elim0)))) v =
 evaluate f (evaluate a v ::ᵥ evaluate b v ::ᵥ evaluate c v ::ᵥ nil) := rfl
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeEvaluation
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentPublishedProvabilityIntroduction.NativeEvaluation
