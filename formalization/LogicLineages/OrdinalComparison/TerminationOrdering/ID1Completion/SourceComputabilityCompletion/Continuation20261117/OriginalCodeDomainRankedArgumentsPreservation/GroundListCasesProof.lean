module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.TypedSpineNilProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.GroundListCasesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel)
open InternalTagArithmeticSupportProof (symm)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def queries : Fin 2 → Program 1 := ![groundList,consOf (constant 1 0) groundList]

theorem successorCases (count types : OTerm alpha) (psi : Formula alpha)
    (hg : Nonempty (Derivation body Delta (graph1 groundList types (suc count))))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (tailTypes : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph1 groundList tailTypes (count.relabel j))) →
      Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode (types.relabel j) z tailTypes)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries ![count] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![count] i).relabel j) = ![count.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  have hc := binaryRecover InternalListCodec.consCode (constant 1 0) groundList
    (ys 1) z (ys 0) ![count.relabel j] (hq 1) (constantValue 0 ![count.relabel j]) (hq 0)
  have hv := Continuation20261117.OriginalSignatureStructure.GroundSupportProof.successorValue
    (count.relabel j) (ys 0) (ys 1) (hq 0) hc
  have hg' := renameInto hg j Theta hj
  simp only [graph1Rename,sucRelabel] at hg'
  have he := valueUnique groundList (ys 1) (types.relabel j) ![suc (count.relabel j)] hv hg'
  have hc' := outputTransport InternalListCodec.consCode (ys 1) (types.relabel j) ![z,ys 0] he hc
  exact next beta j Theta (ys 0) hj (hq 0) hc'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.GroundListCasesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCodeDomainRankedArgumentsPreservation.GroundListCasesProof
