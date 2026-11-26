module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverGuardedExchangeChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationEdgeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel suc z sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (coverOption scratchVertices)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseCoverGuardedExchangeChecks (exact_GuardedExchangeOptionEquality)
open NumberedWindowInternalSparseScalarEdge (exchangeTape)
open NumberedWindowInternalSparseCoverInstallationTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def pairData (C : Program 3) (s : Settings) (baseX : Program 2) (a b va vb : OTerm α) : Formula α :=
  programGraph (guardedExchange C s baseX) (suc z) (exchangeTape a b) ⊓
    (unary (scratchVertices C s) va a ⊓ unary (scratchVertices C s) vb b)

private theorem pairRename {β : Type} (C : Program 3) (s : Settings) (baseX : Program 2) (a b va vb : OTerm α)
    (j : α → β) : (pairData C s baseX a b va vb).relabel j =
    pairData C s baseX (a.relabel j) (b.relabel j) (va.relabel j) (vb.relabel j) := by
  simp only [pairData,conjunctionRename,unaryRename,programRename,exchangeTape,binaryInputsRename,sucRelabel,zRelabel]

private theorem withLeft (C : Program 3) (s : Settings) (baseX : Program 2) (a b va vb x : OTerm α)
    (left : Nonempty (Derivation body Γ (unary (coverOption C s) x a)))
    (d : Nonempty (Derivation body Γ (pairData C s baseX a b va vb))) :
    Nonempty (Derivation body Γ (eqn va vb)) := by
  apply programCases (coverOption C s) ![b] _
  intro β j Θ y keep right
  rw [eqnRelabel]
  rw [unaryInputsRename] at right
  have l := renameInto left j Θ keep
  have r := renameInto d j Θ keep
  rw [unaryRename] at l
  rw [pairRename] at r
  obtain ⟨l⟩ := l
  obtain ⟨r⟩ := r
  obtain ⟨right⟩ := right
  obtain ⟨law⟩ := exact_GuardedExchangeOptionEquality C s baseX body β Θ (a.relabel j) (b.relabel j) (x.relabel j) y
  have equality := Derivation.implicationElimination law (Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft r) (Derivation.conjunctionIntroduction l right))
  obtain ⟨shared⟩ := outputTransport (coverOption C s) (x.relabel j) y ![a.relabel j] ⟨equality⟩ ⟨l⟩
  obtain ⟨compare⟩ := NumberedWindowInternalSparseCoverScratchOpenChecks.exact_SameCoverOptionOutput
    C s body β Θ y (a.relabel j) (b.relabel j) (va.relabel j) (vb.relabel j)
  exact ⟨Derivation.implicationElimination compare (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction shared right) (Derivation.conjunctionRight r))⟩

theorem edgeCover : ExactGuardedEdgeCover := by
  intro C s baseX W body α Γ ctx ty a b va vb
  let X := guardedExchange C s baseX
  let edge := NumberedWindowInternalSparseScalarEdge.edgeGraph X W ctx ty a b
  let vertices := unary (scratchVertices C s) va a ⊓ unary (scratchVertices C s) vb b
  let Δ := (edge ⊓ vertices) :: Γ
  have h : Derivation body Δ (edge ⊓ vertices) := Derivation.hypothesis List.mem_cons_self
  obtain ⟨rule⟩ := NumberedWindowInternalSparseScalarEdgeOpenChecks.exact_OpenPackedScalarEdge X W body α Δ ctx ty a b
  have calls := Derivation.implicationElimination (Derivation.conjunctionLeft rule) (Derivation.conjunctionLeft h)
  have p : Derivation body Δ (pairData C s baseX a b va vb) := Derivation.conjunctionIntroduction
    (Derivation.conjunctionLeft calls) (Derivation.conjunctionRight h)
  have result : Nonempty (Derivation body Δ (eqn va vb)) := by
    apply programCases (coverOption C s) ![a] _
    intro β j Θ x keep left
    rw [eqnRelabel]
    rw [unaryInputsRename] at left
    have d := renameInto ⟨p⟩ j Θ keep
    rw [pairRename] at d
    exact withLeft C s baseX (a.relabel j) (b.relabel j) (va.relabel j) (vb.relabel j) x left d
  obtain ⟨result⟩ := result
  exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverInstallationEdgeProof
