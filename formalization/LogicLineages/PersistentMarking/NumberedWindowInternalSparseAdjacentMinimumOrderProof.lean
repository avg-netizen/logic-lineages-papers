module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumComparisonProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumEdgePoolProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumOrderProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseMinimumEdgePoolProof (acceptedEdgeRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseAdjacentMinimumComparisonProof (compareAt)
open NumberedWindowInternalSparseAdjacentMinimumTargets
attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def edgeMinima (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3)
    (ctx ty a b x y : OTerm α) : Formula α :=
  (leastGraph C X W s ctx ty a x ⊓ leastGraph C X W s ctx ty b y) ⊓ acceptEdge (edge4 X W) ctx ty a b

private theorem inputRename {β : Type} (C : Program 3) (s : Settings) (X : Program 2) (W : Program 3)
    (ctx ty a b x y : OTerm α) (j : α → β) :
    (edgeMinima C s X W ctx ty a b x y).relabel j =
      edgeMinima C s X W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [edgeMinima,conjunctionRename,leastRename,acceptedEdgeRename]

private theorem withLeftPool (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3)
    (ctx ty a b x y va vb pa : OTerm α)
    (input : Nonempty (Derivation body Γ (edgeMinima C s (guardedExchange C s baseX) W ctx ty a b x y)))
    (hva : Nonempty (Derivation body Γ (unary (scratchVertices C s) va a)))
    (hvb : Nonempty (Derivation body Γ (unary (scratchVertices C s) vb b)))
    (hpa : Nonempty (Derivation body Γ (programGraph (membersAtSeed C (guardedExchange C s baseX) W s) pa ![ctx,ty,a])))
    : Nonempty (Derivation body Γ (ltF y x).not) := by
  apply programCases (membersAtSeed C (guardedExchange C s baseX) W s) ![ctx,ty,b] _
  intro β j Θ pb keep run
  change Nonempty (Derivation body Θ ((ltF y x).relabel j).not)
  rw [orderRename]
  rw [tripleInputsRename] at run
  have h := renameInto input j Θ keep
  rw [inputRename] at h
  have rva := renameInto hva j Θ keep
  rw [unaryRename] at rva
  have rvb := renameInto hvb j Θ keep
  rw [unaryRename] at rvb
  have rpa := renameInto hpa j Θ keep
  simp only [programRename,tripleInputsRename] at rpa
  obtain ⟨h⟩ := h
  obtain ⟨rva⟩ := rva
  obtain ⟨rvb⟩ := rvb
  obtain ⟨rpa⟩ := rpa
  obtain ⟨run⟩ := run
  have minima := Derivation.conjunctionLeft h
  exact compareAt C s baseX W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j)
    (va.relabel j) (vb.relabel j) (pa.relabel j) pb (x.relabel j) (y.relabel j)
    (Derivation.conjunctionIntroduction rva (Derivation.conjunctionIntroduction rpa (Derivation.conjunctionLeft minima)))
    (Derivation.conjunctionIntroduction rvb (Derivation.conjunctionIntroduction run (Derivation.conjunctionRight minima)))
    (Derivation.conjunctionRight h)

private theorem withBothVertices (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3)
    (ctx ty a b x y va vb : OTerm α)
    (input : Nonempty (Derivation body Γ (edgeMinima C s (guardedExchange C s baseX) W ctx ty a b x y)))
    (hva : Nonempty (Derivation body Γ (unary (scratchVertices C s) va a)))
    (hvb : Nonempty (Derivation body Γ (unary (scratchVertices C s) vb b)))
    : Nonempty (Derivation body Γ (ltF y x).not) := by
  apply programCases (membersAtSeed C (guardedExchange C s baseX) W s) ![ctx,ty,a] _
  intro β j Θ pa keep run
  change Nonempty (Derivation body Θ ((ltF y x).relabel j).not)
  rw [orderRename]
  rw [tripleInputsRename] at run
  have h := renameInto input j Θ keep
  rw [inputRename] at h
  have rva := renameInto hva j Θ keep
  rw [unaryRename] at rva
  have rvb := renameInto hvb j Θ keep
  rw [unaryRename] at rvb
  exact withLeftPool C s baseX W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j)
    (x.relabel j) (y.relabel j) (va.relabel j) (vb.relabel j) pa h rva rvb run

private theorem withLeftVertices (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3)
    (ctx ty a b x y va : OTerm α)
    (input : Nonempty (Derivation body Γ (edgeMinima C s (guardedExchange C s baseX) W ctx ty a b x y)))
    (hva : Nonempty (Derivation body Γ (unary (scratchVertices C s) va a)))
    : Nonempty (Derivation body Γ (ltF y x).not) := by
  apply programCases (scratchVertices C s) ![b] _
  intro β j Θ vb keep run
  change Nonempty (Derivation body Θ ((ltF y x).relabel j).not)
  rw [orderRename]
  rw [unaryInputsRename] at run
  have h := renameInto input j Θ keep
  rw [inputRename] at h
  have rva := renameInto hva j Θ keep
  rw [unaryRename] at rva
  exact withBothVertices C s baseX W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j)
    (x.relabel j) (y.relabel j) (va.relabel j) vb h rva run

private theorem withMinima (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3)
    (ctx ty a b x y : OTerm α)
    (input : Nonempty (Derivation body Γ (edgeMinima C s (guardedExchange C s baseX) W ctx ty a b x y)))
    : Nonempty (Derivation body Γ (ltF y x).not) := by
  apply programCases (scratchVertices C s) ![a] _
  intro β j Θ va keep run
  change Nonempty (Derivation body Θ ((ltF y x).relabel j).not)
  rw [orderRename]
  rw [unaryInputsRename] at run
  have h := renameInto input j Θ keep
  rw [inputRename] at h
  exact withLeftVertices C s baseX W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j)
    (x.relabel j) (y.relabel j) va h run

theorem order : ExactEdgeMinimumOrder := by
  intro C s baseX W body α Γ ctx ty a b x y
  let A := edgeMinima C s (guardedExchange C s baseX) W ctx ty a b x y
  obtain ⟨d⟩ := withMinima (body := body) (Γ := A :: Γ) C s baseX W ctx ty a b x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumOrderProof
