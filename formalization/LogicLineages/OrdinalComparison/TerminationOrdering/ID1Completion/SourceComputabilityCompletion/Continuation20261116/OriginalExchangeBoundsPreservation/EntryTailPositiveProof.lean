module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryBoundsSuccessProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryTailPositiveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open Continuation20261114 Continuation20261115

theorem nonzero (raw typ head tail param entries tailValue : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw typ head tail)))
    (he : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract (suc entries) raw param)))
    (ht : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.extract tailValue tail param))) :
    Nonempty (Derivation body Delta (eqn tailValue z).not) := by
  have hz : Nonempty (Derivation body ((eqn tailValue z) :: Delta) (eqn tailValue z)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have ht0 := outputTransport ArgumentEntriesRecursor.extract tailValue z ![tail,param] hz (withHyp ht _)
  have hfail := StandaloneConsExtraction.Proof.consFailure body alpha _ raw typ head tail param (withHyp hc _) ht0
  obtain ⟨hbad⟩ := valueUnique ArgumentEntriesRecursor.extract (suc entries) z ![raw,param] (withHyp he _) hfail
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hbad)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryTailPositiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EntryTailPositiveProof
