module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.ChildInputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryKeyProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryWitnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalTagArithmeticSyntaxProof (z)
open OriginalRawSyntaxTransport
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def childKeyQuery : Program 3 := pairOf (.projection 0) (.projection 1)
def valueQuery (n : Nat) : Program 3 := .composition (extract n) ![childKeyQuery,.projection 2]
def depsQuery : Program 3 := consOf childKeyQuery (constant 3 0)
def valuesQuery (n : Nat) : Program 3 := consOf (valueQuery n) (constant 3 0)
def queries (n : Nat) : Fin 4 → Program 3 := ![childKeyQuery,valueQuery n,depsQuery,valuesQuery n]

theorem cases (n : Nat) (child bound param : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (childKey value deps values : OTerm beta),
      (∀ p ∈ Delta, p.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childKey (child.relabel j) (bound.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (extract n) value childKey (param.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode deps childKey z)) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode values value z)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply queryCases (queries n) ![child,bound,param] psi
  intro beta j ys Theta hj hq
  have hx : (fun i => (![child,bound,param] i).relabel j) = ![child.relabel j,bound.relabel j,param.relabel j] := by
    funext i
    fin_cases i <;> rfl
  rw [hx] at hq
  have hk : Nonempty (Derivation body Theta (graph3 childKeyQuery (ys 0) (child.relabel j) (bound.relabel j) (param.relabel j))) := by
    exact hq 0
  have hv : Nonempty (Derivation body Theta (graph3 (valueQuery n) (ys 1) (child.relabel j) (bound.relabel j) (param.relabel j))) := by
    exact hq 1
  have hd : Nonempty (Derivation body Theta (graph3 depsQuery (ys 2) (child.relabel j) (bound.relabel j) (param.relabel j))) := by
    exact hq 2
  have ha : Nonempty (Derivation body Theta (graph3 (valuesQuery n) (ys 3) (child.relabel j) (bound.relabel j) (param.relabel j))) := by
    exact hq 3
  apply next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) hj
  · exact binaryRecover InternalPairing.pairing (.projection 0) (.projection 1) (ys 0) (child.relabel j) (bound.relabel j)
      ![child.relabel j,bound.relabel j,param.relabel j] hk
      (projectionValue 0 ![child.relabel j,bound.relabel j,param.relabel j])
      (projectionValue 1 ![child.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover (extract n) childKeyQuery (.projection 2) (ys 1) (ys 0) (param.relabel j)
      ![child.relabel j,bound.relabel j,param.relabel j] hv hk
      (projectionValue 2 ![child.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover InternalListCodec.consCode childKeyQuery (constant 3 0) (ys 2) (ys 0) z
      ![child.relabel j,bound.relabel j,param.relabel j] hd hk
      (constantValue 0 ![child.relabel j,bound.relabel j,param.relabel j])
  · exact binaryRecover InternalListCodec.consCode (valueQuery n) (constant 3 0) (ys 3) (ys 1) z
      ![child.relabel j,bound.relabel j,param.relabel j] ha hv
      (constantValue 0 ![child.relabel j,bound.relabel j,param.relabel j])
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryWitnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.UnaryWitnessProof
