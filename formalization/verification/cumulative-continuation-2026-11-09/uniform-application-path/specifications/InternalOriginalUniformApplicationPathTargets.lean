module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPathTargets
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)
open InternalOriginalUniformApplicationPath
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Derive the local starting invariant from the original normalized source
typing and symbolic parameter-pair graph, then use concrete reflexive lifting.
Neither invariant preservation nor single-edge compatibility is a hypothesis. -/
def ActualOriginalUniformReflexiveApplicationPath : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (oldStep : Program 4) (oldVertex : Program 5),
  RuntimePathLaw n (normalizeData data) oldStep oldVertex false

/-- The same original positive path checker and same map, with its literal
nil rejection. The source antecedent has no additional starting invariant. -/
def ActualOriginalUniformPositiveApplicationPath : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (data : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity data →
  ∀ (oldStep : Program 4) (oldVertex : Program 5),
  RuntimePathLaw n (normalizeData data) oldStep oldVertex true

/-- ONE base Data, old step and original fallback vertex precede every
window, Gamma, body, type and arithmetic input. Retain the original canonical
package, edge/application/vertex/map calibration, both all-input path functions
and both runtime path laws. Outer Object/context wrappers and unqualified
CertifiedApplicationLift are separate obligations. -/
def ActualOriginalUniformApplicationPathSelection : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ data : Data, ∃ oldStep : Program 4, ∃ oldVertex : Program 5,
    InternalOriginalUniformDescentSelection.Calibrated n arity data ∧
    InternalOriginalUniformApplicationStepSelection.LeafCalibrated n arity oldStep ∧
    InternalOriginalUniformVertexPath.OldVertexCalibrated n arity oldVertex ∧
    InternalOriginalUniformApplicationTyping.RetainedNormalizedPackage n arity data ∧
    InternalParameterizedCanonicalQuotientEdgeApplicationLift.SelectedCalibrated
      n arity (normalizeData data) oldStep ∧
    InternalOriginalUniformVertexPath.SelectedCalibrated
      n arity (normalizeData data) oldVertex ∧
    PathCalibrated n arity (normalizeData data) oldStep ∧
    RuntimePathLaw n (normalizeData data) oldStep oldVertex false ∧
    RuntimePathLaw n (normalizeData data) oldStep oldVertex true

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPathTargets
