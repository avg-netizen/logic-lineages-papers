module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportConstructorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportContextProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendFrameQueryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open InternalTagArithmeticSyntaxProof (eqn)
open InternalTagArithmeticSupportProof
open OriginalTypedDecoderTransport
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem iffRename {beta : Type} (P Q : Formula alpha) (j : alpha → beta) :
    (P.iff Q).relabel j = (P.relabel j).iff (Q.relabel j) := rfl

theorem notRename {beta : Type} (P : Formula alpha) (j : alpha → beta) :
    P.not.relabel j = (P.relabel j).not := rfl

theorem closedApply {P Q : Formula alpha}
    (h : Nonempty (Derivation body [] (P.imp Q)))
    (hp : Nonempty (Derivation body Delta P)) : Nonempty (Derivation body Delta Q) := by
  obtain ⟨h⟩ := weakenProof h (Delta := Delta) (by intro p hp; cases hp)
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination h hp⟩

theorem iffForward {P Q : Formula alpha}
    (h : Nonempty (Derivation body Delta (P.iff Q)))
    (hp : Nonempty (Derivation body Delta P)) : Nonempty (Derivation body Delta Q) := by
  obtain ⟨h⟩ := h
  obtain ⟨hp⟩ := hp
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft h) hp⟩

theorem iffBackward {P Q : Formula alpha}
    (h : Nonempty (Derivation body Delta (P.iff Q)))
    (hq : Nonempty (Derivation body Delta Q)) : Nonempty (Derivation body Delta P) := by
  obtain ⟨h⟩ := h
  obtain ⟨hq⟩ := hq
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight h) hq⟩

theorem equalReflexive (t : OTerm alpha) : Nonempty (Derivation body Delta (equal t t)) := by
  rw [equalEqn]
  exact ⟨refl t⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportLogicalProof
