module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformObjectPathDispatch
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The same globally calibrated Data and old vertex precede every source
window. At the selected original window, the runtime Object chooses Gamma.
Every raw five-vector is retained; there is no valid-object, typing, nonzero,
successful decoding or path-acceptance restriction on this equality. -/
def ActualOriginalUniformObjectPathCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data) (oldVertex oldLift : Program 5),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  InternalOriginalUniformVertexPath.OldVertexCalibrated n arity oldVertex →
  PathValueCalibrated n arity oldLift →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  PathValueCalibrated n arity
    (dispatch (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (InternalOriginalUniformVertexPath.vertex data oldVertex) oldLift)

/-- At the selected context, the supplied outer output is EXACTLY the
original map output at the actual parameter pair. GammaCode, the raw payload,
all type codes and every certificate remain symbolic. No semantic reflection,
invariant, typedness or path preservation is assumed. -/
def ActualInternalOriginalUniformObjectPathActiveGraph : Prop :=
  ∀ (window : Nat) (vertexProgram oldLift : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain gammaCode argumentObject argument parameter certificate out : OTerm α),
  Nonempty (Derivation body Delta
    ((activePremises window context gammaCode argumentObject argument parameter).imp
      ((dispatchGraph window vertexProgram oldLift
          out context domain codomain argumentObject certificate).iff
        (InternalApplicationPathMap.mapGraph vertexProgram
          out certificate parameter domain codomain argument))))

/-- A literal zero graph for the selected-window test recovers the whole
original fallback with the same result and all five inputs unchanged. -/
def ActualInternalOriginalUniformObjectPathZeroGraph : Prop :=
  ∀ (window : Nat) (vertexProgram oldLift : Program 5)
    (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (context domain codomain argumentObject certificate out : OTerm α),
  Nonempty (Derivation body Delta
    ((windowGraph window OrdinaryArithmetic.zeroTerm
        context domain codomain argumentObject certificate).imp
      ((dispatchGraph window vertexProgram oldLift
          out context domain codomain argumentObject certificate).iff
        (oldLiftGraph oldLift out context domain codomain argumentObject certificate))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformObjectPathDispatchTargets
