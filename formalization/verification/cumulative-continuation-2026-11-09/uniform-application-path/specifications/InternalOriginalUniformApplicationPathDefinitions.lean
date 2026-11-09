module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedCanonicalQuotientEdgeApplicationLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPath
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original closed domain/codomain codes and the RAW argument, with the
same runtime parameter in the existing mapper's former context coordinate. -/
def parameters {α : Type} (sigma tau : Ty) (parameter argument : OTerm α) :
    InternalParameterizedApplicationPathLift.Parameters α :=
  InternalApplicationPathMap.parameters parameter
    (numeral (typeNumber sigma)) (numeral (typeNumber tau)) argument

/-- The source pair graph, source/argument typing, original path acceptance,
both actual vertex outputs and the original map output. The initial local
invariant and all per-edge rules are conclusions of earlier proofs. -/
def pathPremises {α : Type} (window : Nat) (data : Data)
    (oldStep : Program 4) (oldVertex : Program 5) (positive : Bool) (sigma tau : Ty)
    (parameter gammaCode x y argument certificate out other mapped : OTerm α) : Formula α :=
  InternalOriginalUniformVertexPath.initialPremises window data sigma tau parameter gammaCode argument x ⊓
    (InternalParameterizedPathChecker.checkerGraph
      (InternalParameterizedQuotientEdgeChecker.checker data oldStep) positive
      InternalOriginalStepGuard.one x y certificate parameter ⊓
      (InternalParameterizedApplicationPathLift.vertexAt
        (InternalOriginalUniformVertexPath.vertex data oldVertex)
        (parameters sigma tau parameter argument) out x ⊓
        (InternalParameterizedApplicationPathLift.vertexAt
          (InternalOriginalUniformVertexPath.vertex data oldVertex)
          (parameters sigma tau parameter argument) other y ⊓
          InternalParameterizedApplicationPathLift.mappedAt
            (InternalOriginalUniformVertexPath.vertex data oldVertex)
            (parameters sigma tau parameter argument) mapped certificate)))

/-- Gamma's code stays symbolic. No fixed fiber, target typing, codomain
membership, initial invariant or local compatibility rule is an antecedent. -/
def RuntimePathLaw (n : Nat) (data : Data) (oldStep : Program 4)
    (oldVertex : Program 5) (positive : Bool) : Prop :=
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α)) (sigma tau : Ty)
    (parameter gammaCode x y argument certificate out other mapped : OTerm α),
  Nonempty (Derivation body Delta
    ((pathPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
      data oldStep oldVertex positive sigma tau
      parameter gammaCode x y argument certificate out other mapped).imp
      (InternalParameterizedPathChecker.checkerGraph
        (InternalParameterizedQuotientEdgeChecker.checker data oldStep) positive
        InternalOriginalStepGuard.one out other mapped parameter)))

/-- Both original path functions retain every natural input at each source
parameter slice, including nil, malformed and rejected certificate codes. -/
def PathCalibrated (n : Nat) (arity : Fin n → Nat) (data : Data) (oldStep : Program 4) : Prop :=
  ∀ (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ x y certificate : Nat,
    (evaluate (InternalParameterizedPathChecker.checker
        (InternalParameterizedQuotientEdgeChecker.checker data oldStep) false)
      (x ::ᵥ y ::ᵥ certificate ::ᵥ
        InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table ::ᵥ List.Vector.nil) =
      if NumberedQuotientPathCertificates.pathTest n arity symbols S Gamma table x y
        ((NumberedQuotientPathCertificates.decodePathCertificate certificate).getD []) then 1 else 0) ∧
    (evaluate (InternalParameterizedPathChecker.checker
        (InternalParameterizedQuotientEdgeChecker.checker data oldStep) true)
      (x ::ᵥ y ::ᵥ certificate ::ᵥ
        InternalOriginalUniformParameterLeaves.parameterCode symbols S Gamma table ::ᵥ List.Vector.nil) =
      if NumberedQuotientPathCertificates.positivePathTest n arity symbols S Gamma table
        x y certificate then 1 else 0)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationPath
