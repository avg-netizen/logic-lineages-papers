module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.PositiveDepthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.AcceptanceProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroDepthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem fieldsZeroImpossible (n : Nat) (raw bound types heads labels tupleBound : OTerm alpha)
    (hf : Nonempty (Derivation body Delta
      (OriginalEnumerationFields.Targets.accepted n raw bound types heads labels tupleBound)))
    (hb : Nonempty (Derivation body Delta (Targets.depthBound n raw z))) :
    Nonempty (Derivation body Delta ⊥) :=
  PositiveDepthProof.zeroImpossible n raw
    (OriginalEnumerationFields.AcceptanceProof.validFromFields n ![raw,bound,types,heads,labels,tupleBound] hf) hb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroDepthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.ZeroDepthProof
