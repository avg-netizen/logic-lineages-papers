module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenConsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalControlGraphSupportProof (outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursion (recGraph)
open ID1Completion.InternalRawListRecursionProof (consForward stepCases)
open ID1Completion.InternalQuotientComparisonProof (orLeft orRight)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseDirectedSeen
open NumberedWindowInternalSparseDirectedSeenOpenSyntaxProof (scanImplies impliesRename witnessRename)
open NumberedWindowInternalSparseDirectedSeenOpenRowProof (rowCases)
open NumberedWindowInternalSparseDirectedSeenOpenWitnessProof (atHead fromTail)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem afterRow (E : Program 4) (code w tail prior ctx ty v : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code w tail)))
    (inherited : Nonempty (Derivation body Γ (scanImplies E tail ctx ty v)))
    (tailResult : Nonempty (Derivation body Γ (programGraph (scan E) prior (scanTape tail ctx ty v))))
    (result : Nonempty (Derivation body Γ (programGraph (scanStep E) (suc z) (rowTape w prior ctx ty v)))) :
    Nonempty (Derivation body Γ (seenWitness E code ctx ty v)) := by
  let P := eqn w v
  let Q := acceptEdge E ctx ty w v
  let T := eqn prior (suc z)
  obtain ⟨split⟩ := rowCases E w prior ctx ty v result
  obtain ⟨cell⟩ := cell
  obtain ⟨ih⟩ := inherited
  obtain ⟨tailResult⟩ := tailResult
  obtain ⟨eqHit⟩ := atHead (body := body) (Γ := P :: Γ) E code w tail ctx ty v
    ⟨addHyp cell P⟩ ⟨orLeft (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨edgeHit⟩ := atHead (body := body) (Γ := Q :: Γ) E code w tail ctx ty v
    ⟨addHyp cell Q⟩ ⟨orRight (Derivation.hypothesis List.mem_cons_self)⟩
  have sameTail := outputTransport (body := body) (Gamma := T :: Γ) (scan E)
    prior (suc z) (scanTape tail ctx ty v) ⟨Derivation.hypothesis List.mem_cons_self⟩
    ⟨addHyp tailResult T⟩
  obtain ⟨sameTail⟩ := sameTail
  obtain ⟨tailHit⟩ := fromTail (body := body) (Γ := T :: Γ) E code w tail ctx ty v
    ⟨addHyp cell T⟩ ⟨Derivation.implicationElimination (addHyp ih T) sameTail⟩
  have hOther : Derivation body ((Q ⊔ T) :: Γ) (seenWitness E code ctx ty v) :=
    disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp (Derivation.implicationIntroduction edgeHit) (Q ⊔ T))
      (addHyp (Derivation.implicationIntroduction tailHit) (Q ⊔ T))
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction eqHit)
    (Derivation.implicationIntroduction hOther)⟩

/-- Recover the actual tail output tied to this same physical cons,
rather than assuming a decoded list or assigning a default tail value. -/
theorem consScan (E : Program 4) (code w tail ctx ty v : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code w tail)))
    (ih : Nonempty (Derivation body Γ (scanImplies E tail ctx ty v)))
    (accepted : Nonempty (Derivation body Γ (scanGraph E code ctx ty v))) :
    Nonempty (Derivation body Γ (seenWitness E code ctx ty v)) := by
  have step := consForward (constantZero 3) (scanStep E) code w tail (suc z)
    (![ctx,ty,v] : Fin 3 → OTerm α) cell accepted
  apply stepCases (constantZero 3) (scanStep E) (suc z) w tail
    (![ctx,ty,v] : Fin 3 → OTerm α) (seenWitness E code ctx ty v) step
  intro β j Δ prior keep tailResult running
  rw [tripleInputsRename] at tailResult running
  simp only [sucRelabel,zRelabel] at running
  rw [witnessRename]
  have c := renameInto cell j Δ keep
  rw [consGraphRename] at c
  have h := renameInto ih j Δ keep
  rw [impliesRename] at h
  exact afterRow E (code.relabel j) (w.relabel j) (tail.relabel j) prior
    (ctx.relabel j) (ty.relabel j) (v.relabel j) c h tailResult running

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenOpenConsProof
