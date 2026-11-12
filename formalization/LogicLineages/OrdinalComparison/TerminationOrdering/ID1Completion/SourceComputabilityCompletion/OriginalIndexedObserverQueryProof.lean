module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Bind two actual outputs of an arbitrary binary Program at one unchanged
parameter. The composition recovery is checked while the Program is abstract. -/
theorem indexedPairOutputCases (p : Program 3)
    (left right parameter cutoff : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (leftOut rightOut : OrdinaryArithmetic.Term β),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph3 p leftOut (cutoff.relabel j) (left.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta
        (graph3 p rightOut (cutoff.relabel j) (right.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin 2 → Program 4 :=
    ![.composition p ![.projection 3,.projection 0,.projection 2],
      .composition p ![.projection 3,.projection 1,.projection 2] ]
  let xs : Fin 4 → OrdinaryArithmetic.Term α := ![left,right,parameter,cutoff]
  apply InternalApplicationStepPeelSupportProof.queryCases qs xs psi
  intro β j ys Delta hj hq
  let xx : Fin 4 → OrdinaryArithmetic.Term β :=
    ![left.relabel j,right.relabel j,parameter.relabel j,cutoff.relabel j]
  have hxs : (fun a => (xs a).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
  rw [hxs] at hq
  have hf := InternalAcceptanceSupportProof.compositionRecover p
    (![.projection 3,.projection 0,.projection 2] : Fin 3 → Program 4) (ys 0) xx
    (Fin.cons (cutoff.relabel j) (Fin.cons (left.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) (hq 0)
    (fun i => Fin.cases (projectionValue 3 xx) (Fin.cases (projectionValue 0 xx)
      (Fin.cases (projectionValue 2 xx) (fun k => Fin.elim0 k))) i)
  have ha := InternalAcceptanceSupportProof.compositionRecover p
    (![.projection 3,.projection 1,.projection 2] : Fin 3 → Program 4) (ys 1) xx
    (Fin.cons (cutoff.relabel j) (Fin.cons (right.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) (hq 1)
    (fun i => Fin.cases (projectionValue 3 xx) (Fin.cases (projectionValue 1 xx)
      (Fin.cases (projectionValue 2 xx) (fun k => Fin.elim0 k))) i)
  exact h β j Delta (ys 0) (ys 1) hj hf ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalIndexedObserverQueryProof
