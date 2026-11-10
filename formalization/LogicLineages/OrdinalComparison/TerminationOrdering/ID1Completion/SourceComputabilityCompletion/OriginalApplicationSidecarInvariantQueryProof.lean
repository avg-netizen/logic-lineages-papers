module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Bind two actual outputs of an arbitrary binary Program at one unchanged
parameter. The composition recovery is checked while the Program is abstract. -/
theorem binaryPairOutputCases (p : Program 2)
    (left right parameter : OrdinaryArithmetic.Term α) (psi : Formula α)
    (h : ∀ (β : Type) (j : α → β) (Delta : List (Formula β))
      (leftOut rightOut : OrdinaryArithmetic.Term β),
      (∀ r ∈ Gamma, r.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta
        (graph2 p leftOut (left.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 p rightOut (right.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  let qs : Fin 2 → Program 3 :=
    ![.composition p ![.projection 0,.projection 2],
      .composition p ![.projection 1,.projection 2] ]
  let xs : Fin 3 → OrdinaryArithmetic.Term α := ![left,right,parameter]
  apply InternalApplicationStepPeelSupportProof.queryCases qs xs psi
  intro β j ys Delta hj hq
  let xx : Fin 3 → OrdinaryArithmetic.Term β :=
    ![left.relabel j,right.relabel j,parameter.relabel j]
  have hxs : (fun a => (xs a).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · refine Fin.cases ?_ (fun i => ?_) i
      · rfl
      · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
        rfl
  rw [hxs] at hq
  have hqf : Nonempty (Derivation body Delta
      (programGraph (.composition p ![.projection 0,.projection 2]) (ys 0) xx)) := hq 0
  have hqa : Nonempty (Derivation body Delta
      (programGraph (.composition p ![.projection 1,.projection 2]) (ys 1) xx)) := hq 1
  have hf : Nonempty (Derivation body Delta
      (graph2 p (ys 0) (left.relabel j) (parameter.relabel j))) :=
    binaryRecover p (.projection 0) (.projection 2)
      (ys 0) (left.relabel j) (parameter.relabel j) xx hqf
      (projectionValue 0 xx) (projectionValue 2 xx)
  have ha : Nonempty (Derivation body Delta
      (graph2 p (ys 1) (right.relabel j) (parameter.relabel j))) :=
    binaryRecover p (.projection 1) (.projection 2)
      (ys 1) (right.relabel j) (parameter.relabel j) xx hqa
      (projectionValue 1 xx) (projectionValue 2 xx)
  exact h β j Delta (ys 0) (ys 1) hj hf ha

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarInvariantQueryProof
