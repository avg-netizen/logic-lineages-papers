module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibration
open Source
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformParameterLeaves (parameterObject)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The EXISTING literal window-guarded vertex, not the historical vertex
without a global window guard. All program inputs precede every raw input. -/
abbrev vertex (data : Data) (window : Program 1) (oldVertex : Program 5) : Program 5 :=
  Path.vertex data window oldVertex

/-- The unchanged ORIGINAL raw-list map and original entry/edge encoding. -/
abbrev pathMap (data : Data) (window : Program 1) (oldVertex : Program 5) : Program 5 :=
  InternalApplicationPathMap.pathMap (vertex data window oldVertex)

/-- Original all-input native semantics. The caller's raw context is retained,
including malformed contexts and nonclosed windows. A single original Gamma
is shared by every vertex coordinate and every original path certificate at
one raw parameter. There is no raw-context encoding converse premise. -/
structure Calibrated (n : Nat) (arity : Fin n → Nat)
    (data : Data) (window : Program 1) (oldVertex : Program 5) : Prop where
  vertex : ∀ v : List.Vector Nat 5,
    evaluate (RuntimePathCalibration.vertex data window oldVertex) v =
      RuntimeVertex.value n arity v
  slices : ∀ parameter : Nat, ∃ Gamma : List Ty,
    (∀ value : Nat, parameterObject value parameter = some (Gamma,value)) ∧
    (∀ domain codomain argument value : Nat,
      evaluate (RuntimePathCalibration.vertex data window oldVertex)
          (List.Vector.ofFn ![parameter,domain,codomain,argument,value]) =
        ApplicationCertificateLiftPath.vertex n arity Gamma (Nat.unpair parameter).1
          domain codomain argument value) ∧
    (∀ domain codomain argument certificate : Nat,
      evaluate (pathMap data window oldVertex)
          (List.Vector.ofFn ![certificate,parameter,domain,codomain,argument]) =
        ApplicationCertificateLiftPath.liftPath n arity Gamma (Nat.unpair parameter).1
          domain codomain argument certificate)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimePathCalibration
