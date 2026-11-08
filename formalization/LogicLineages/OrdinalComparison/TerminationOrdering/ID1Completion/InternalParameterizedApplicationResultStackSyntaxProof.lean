module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalParameterizedApplicationResultStack
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

@[simp] theorem appendParameterLast {n : Nat} {α : Type} (xs : Fin n → α) (p : α) :
    appendParameter xs p (Fin.last n) = p := Fin.lastCases_last

@[simp] theorem appendParameterCastSucc {n : Nat} {α : Type} (xs : Fin n → α) (p : α) (i : Fin n) :
    appendParameter xs p i.castSucc = xs i := Fin.lastCases_castSucc i

theorem appendParameterRename {n : Nat} {α β : Type}
    (xs : Fin n → OTerm α) (p : OTerm α) (j : α → β) :
    (fun i => (appendParameter xs p i).relabel j) =
      appendParameter (fun i => (xs i).relabel j) (p.relabel j) := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp only [appendParameterLast]
  · simp only [appendParameterCastSucc]

theorem appendParameterOne {α : Type} (value parameter : α) :
    appendParameter (Fin.cons value Fin.elim0) parameter =
      Fin.cons value (Fin.cons parameter Fin.elim0) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
    rfl

theorem appendParameterFour {α : Type} (d e f a parameter : α) :
    appendParameter (Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a Fin.elim0)))) parameter =
      Fin.cons d (Fin.cons e (Fin.cons f (Fin.cons a (Fin.cons parameter Fin.elim0)))) := by
  funext i
  refine Fin.cases ?_ (fun k => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun k => ?_) k
    · rfl
    · refine Fin.cases ?_ (fun k => ?_) k
      · rfl
      · refine Fin.cases ?_ (fun k => ?_) k
        · rfl
        · refine Fin.cases ?_ (fun k => Fin.elim0 k) k
          rfl

@[simp] theorem liftRename {α β : Type} (P : Program 1) (out value parameter : OTerm α) (j : α → β) :
    (graph2 (liftP P) out value parameter).relabel j =
      graph2 (liftP P) (out.relabel j) (value.relabel j) (parameter.relabel j) :=
  graph2Rename _ _ _ _ _

@[simp] theorem wireRename {n : Nat} {α β : Type} (P : Program (n+1))
    (selectors : Fin n → Program 1) (out state parameter : OTerm α) (j : α → β) :
    (graph2 (wireP P selectors) out state parameter).relabel j =
      graph2 (wireP P selectors) (out.relabel j) (state.relabel j) (parameter.relabel j) :=
  graph2Rename _ _ _ _ _

@[simp] theorem transitionRename {α β : Type} (guard leaf : Program 2) (combine : Program 5)
    (out state parameter : OTerm α) (j : α → β) :
    (graph2 (transitionP guard leaf combine) out state parameter).relabel j =
      graph2 (transitionP guard leaf combine) (out.relabel j) (state.relabel j) (parameter.relabel j) :=
  graph2Rename _ _ _ _ _

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationResultStackSyntaxProof
