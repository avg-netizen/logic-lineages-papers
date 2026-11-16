module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonConsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonSpineProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem impossible (tag : Nat) (h6 : tag ≠ 6) (h7 : tag ≠ 7) (raw param entries : OTerm alpha) (psi : Formula alpha)
    (ht : Nonempty (Derivation body Delta (graph1 InternalUnpair.left (numeral tag) raw)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param))) :
    Nonempty (Derivation body Delta psi) := by
  have hn7 : Nonempty (Derivation body Delta (eqn (numeral tag) (numeral 7)).not) := by
    simpa only [equalEqn] using
      (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNe (body := body) (Delta := Delta) tag 7 h7)
  have hn6 : Nonempty (Derivation body Delta (ArgumentEntriesNonConsCoherence.StepProof.caseFormula false (numeral tag))) := by
    change Nonempty (Derivation body Delta (eqn (numeral tag) (numeral 6)).not)
    simpa only [equalEqn] using
      (OriginalRawSyntaxTransportInternalConstructorSupportProof.numeralNe (body := body) (Delta := Delta) tag 6 h6)
  have hz := EntryNonConsProof.nonCons false raw (numeral tag) param ht hn7 hn6
  obtain ⟨hb⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) z ![raw,param] he hz
  exact ⟨Derivation.explosion (sucNeZeroApply hb)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonSpineProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryNonSpineProof
