module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceBranchAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceRemoveBranchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof (programCases)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel sucRelabel zRelabel)
open EraseAbsence EraseAbsenceSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem remove (list head tail needle acc rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 Erase.state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc z rest)))
    (he : Nonempty (Derivation body Delta (eqn head needle)))
    (ha : Nonempty (Derivation body Delta (graph2 Erase.state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (result list needle bit)) := by
  apply programCases InternalPairing.pairing ![suc z,rest] _
  intro beta j Theta out hj ho
  have hx : (fun i => (![suc z,rest] i).relabel j) = ![suc z,rest.relabel j] := by
    funext i
    fin_cases i
    · change (suc (z : OTerm alpha)).relabel j = suc z
      simp only [sucRelabel,zRelabel]
    · rfl
  rw [hx] at ho
  rw [resultRename]
  have hcj := renameInto hc j Theta hj
  have htj := renameInto ht j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have haj := renameInto ha j Theta hj
  have hapj := renameInto hap j Theta hj
  simp only [graph2Rename,zRelabel] at hcj htj hpj haj hapj
  rw [eqnRelabel] at hej
  obtain ⟨hv,hr⟩ := EraseAbsenceBranchAtProof.remove (list.relabel j) (head.relabel j) (tail.relabel j)
    (needle.relabel j) (acc.relabel j) (rest.relabel j) out hcj htj hpj hej ho
  exact EraseAbsenceOutputProof.transfer (list.relabel j) (needle.relabel j) out (suc z) (rest.relabel j)
    (actual.relabel j) (bit.relabel j) (remaining.relabel j) hv ho haj hapj hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceRemoveBranchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseAbsenceRemoveBranchProof
