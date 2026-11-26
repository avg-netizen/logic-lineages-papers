module
public import LogicLineages.PersistentMarking.NumberedWindowInternalPairedProjectedConsTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalPairedProjectedConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalControlGraphSupportProof (equalEqn valueUnique headTransport)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalDirectTargetMapCons (exactOpenTargetMapCons)
open NumberedWindowInternalDirectInsertedTargetsMapTargets (scratchTargets)
open NumberedWindowInternalPairedProjectedConsTargets

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem pinHead (code earlier later tail : OTerm α)
    (same : D B Γ (eqn earlier later)) (cell : D B Γ (consGraph code earlier tail)) :
    D B Γ (consGraph code later tail) :=
  headTransport consCode code earlier later (Fin.cons tail Fin.elim0) same cell

/-- Both genuine map results project the same physical head row.
Recover the two actual tail map results and pin the decoded target using
functionality of the literal field-zero graph, not a value-level equality. -/
theorem exact_OpenPairedProjectedCons : ExactOpenPairedProjectedCons := by
  intro B α Γ left right row tailL tailR projL projR goal cellL cellR mapL mapR k
  apply exactOpenTargetMapCons B α Γ left row tailL projL goal cellL mapL
  intro β j Δ tL prevL keep _ f0L tailMapL packedL
  have cellR' := renameInto cellR j Δ keep
  rw [consGraphRename] at cellR'
  have mapR' := renameInto mapR j Δ keep
  rw [unaryRename, sucRelabel] at mapR'
  apply exactOpenTargetMapCons B β Δ (right.relabel j) (row.relabel j)
    (tailR.relabel j) (projR.relabel j) (goal.relabel j) cellR' mapR'
  intro γ k' Ω tR prevR keep' _ f0R tailMapR packedR
  have f0L' := renameInto f0L k' Ω keep'
  rw [unaryRename] at f0L'
  have same := valueUnique (field 0) tR (tL.relabel k')
    ![((row.relabel j).relabel k')] f0R f0L'
  have packedR' := pinHead ((projR.relabel j).relabel k') tR (tL.relabel k') prevR same packedR
  have tailMapL' := renameInto tailMapL k' Ω keep'
  rw [unaryRename,sucRelabel] at tailMapL'
  have packedL' := renameInto packedL k' Ω keep'
  rw [consGraphRename] at packedL'
  have retained : ∀ f ∈ Γ, f.relabel (k' ∘ j) ∈ Ω := by
    intro f h
    rw [← formulaRelabelComposition]
    exact keep' _ (keep f h)
  rw [formulaRelabelComposition]
  exact k γ (k' ∘ j) Ω (tL.relabel k') (prevL.relabel k') prevR retained
    (by simpa only [Term.relabel_relabel] using tailMapL')
    (by simpa only [Term.relabel_relabel] using tailMapR)
    (by simpa only [Term.relabel_relabel] using packedL')
    (by simpa only [Term.relabel_relabel] using packedR')

#print axioms exact_OpenPairedProjectedCons

end LogicLineages.PersistentMarking.NumberedWindowInternalPairedProjectedConsProof
