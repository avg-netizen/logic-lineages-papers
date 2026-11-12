module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaChildProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCasePayloadProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof
open OriginalLambdaConstructor OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaConstructorGraphSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Query the actual raw payload without discarding the original codomain.
This is proof-only constructor algebra, not an erasure or source oracle. -/
theorem packedFromFields (s d e child arrow : OTerm alpha) (psi : Formula alpha)
    (hf : Nonempty (Derivation body Delta (Fields s d e child arrow)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (raw : OTerm beta), (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta
        (graph3 packedLambda (s.relabel j) (d.relabel j) (e.relabel j) raw)) →
      Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
  apply OriginalPackedSourceLambdaChildProof.rawCoordinates s child d e arrow psi hf
  intro beta j Theta node inner raw hj ho hn hi hb
  have hf' := renameInto hf j Theta hj
  rw [fieldsRename] at hf'
  have hp := packedAtPairs (s.relabel j) (d.relabel j) (e.relabel j) raw
    (arrow.relabel j) inner node (andLeft (andRight (andRight hf'))) hi hn ho
  exact next beta j Theta raw hj hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCasePayloadProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureCasePayloadProof
