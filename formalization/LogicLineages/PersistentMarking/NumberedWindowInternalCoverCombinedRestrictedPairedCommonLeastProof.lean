module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedMinimumProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScalarEdgeOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename outputTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (congSuc symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (hasRename casesLeast)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalCoverCombinedRestrictedPairedMinimumProof
  (exact_OpenCoverCombinedRestrictedPairedEdge)
open NumberedWindowInternalCoverCombinedRestrictedWrapperReportProof
  (exact_OpenCoverThinMatchingWindowReport)
open NumberedWindowInternalSparseScalarEdgeOpenChecks (exact_OpenPackedScalarEdge)
open NumberedWindowInternalSparseAdjacentMinimumChecks (exact_MutualEdgeMinimumEquality)
open NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastTargets

attribute [local irreducible] programGraph

private theorem edgeRename {α β : Type} (X : Program 2) (W : Program 3) (ctx ty a b : OTerm α)
    (j : α → β) :
    (edgeGraph X W ctx ty a b).relabel j =
      edgeGraph X W (ctx.relabel j) (ty.relabel j) (a.relabel j) (b.relabel j) := by
  simp only [edgeGraph,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]

/-- Mutual edges and a held least at `a` give the least at `b` at the same value,
from any successful least at `b` (which is then eliminated). -/
private theorem shareLeast {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (C : Program 3) (s : Settings) (baseX : Program 2) (W : Program 3) (ctx ty a b x : OTerm α)
    (ab : Nonempty (Derivation body Γ (edgeGraph (guardedExchange C s baseX) W ctx ty a b)))
    (ba : Nonempty (Derivation body Γ (edgeGraph (guardedExchange C s baseX) W ctx ty b a)))
    (la : Nonempty (Derivation body Γ (leastGraph C (guardedExchange C s baseX) W s ctx ty a x)))
    (hb : Nonempty (Derivation body Γ
      (NumberedWindowInternalSparsePackedDomainTargets.hasLeast C (guardedExchange C s baseX) W s ctx ty b))) :
    Nonempty (Derivation body Γ (leastGraph C (guardedExchange C s baseX) W s ctx ty b x)) := by
  let X := guardedExchange C s baseX
  apply casesLeast C X W s ctx ty b (leastGraph C X W s ctx ty b x) hb
  intro β i Θ y keep ly
  rw [leastRename]
  have ab' := renameInto ab i Θ keep
  have ba' := renameInto ba i Θ keep
  have la' := renameInto la i Θ keep
  rw [edgeRename] at ab' ba'
  rw [leastRename] at la'
  obtain ⟨ab'⟩ := ab'
  obtain ⟨ba'⟩ := ba'
  obtain ⟨la'⟩ := la'
  obtain ⟨ly⟩ := ly
  obtain ⟨law⟩ := exact_MutualEdgeMinimumEquality C s baseX W body β Θ
    (ctx.relabel i) (ty.relabel i) (a.relabel i) (b.relabel i) (x.relabel i) y
  have eq : Derivation body Θ (eqn (x.relabel i) y) :=
    Derivation.implicationElimination law (Derivation.conjunctionIntroduction
      (Derivation.conjunctionIntroduction la' ly) (Derivation.conjunctionIntroduction ab' ba'))
  exact outputTransport (packedLeastProgram C X W s) (suc y) (suc (x.relabel i))
    ![ctx.relabel i,ty.relabel i,b.relabel i] ⟨congSuc (symm eq)⟩ ⟨ly⟩

theorem exact_OpenCoverCombinedRestrictedPairedCommonLeast :
    ExactOpenCoverCombinedRestrictedPairedCommonLeast := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m goal P W D X a b syn ty argument
    fg gf ma mb k
  have ab := exact_OpenCoverCombinedRestrictedPairedEdge V TV M M0 B T base s body α Γ
    ctx dom cod f g arg m syn ty argument fg gf ma mb
  have ba := exact_OpenCoverCombinedRestrictedPairedEdge V TV M M0 B T base s body α Γ
    ctx dom cod g f arg m syn ty argument gf fg mb ma
  obtain ⟨law⟩ := exact_OpenPackedScalarEdge X W body α Γ ctx cod a b
  obtain ⟨abd⟩ := ab
  have windows := Derivation.conjunctionRight
    (Derivation.implicationElimination (Derivation.conjunctionLeft law) abd)
  obtain ⟨repA⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V X s body α Γ ctx cod a
    ⟨Derivation.conjunctionLeft windows⟩
  obtain ⟨repB⟩ := exact_OpenCoverThinMatchingWindowReport P.cover P.W P.V X s body α Γ ctx cod b
    ⟨Derivation.conjunctionRight windows⟩
  apply casesLeast P.cover X W s ctx cod a goal ⟨Derivation.conjunctionRight repA⟩
  intro β j Δ x keep la
  have hb := renameInto ⟨Derivation.conjunctionRight repB⟩ j Δ keep
  rw [hasRename] at hb
  have ab' := renameInto ⟨abd⟩ j Δ keep
  have ba' := renameInto ba j Δ keep
  rw [edgeRename] at ab' ba'
  have lb := shareLeast P.cover s (thinPairedExchange D) W (ctx.relabel j) (cod.relabel j)
    (a.relabel j) (b.relabel j) x ab' ba' la hb
  exact k β j Δ x keep la lb

#print axioms exact_OpenCoverCombinedRestrictedPairedCommonLeast
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedCommonLeastProof
