module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedMinimumTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAdjacentMinimumChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedMinimumProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (quadInputsRename)
open NumberedWindowInternalSparseScalarEdge (edgeGraph)
open NumberedWindowInternalSparseDirectedSeen (edgeTape)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalCoverCombinedRestrictedCrossCoverPairedProof
  (exact_OpenCoverCombinedRestrictedPairedCrossCover)
open NumberedWindowInternalSparseAdjacentMinimumChecks (exact_MutualEdgeMinimumEquality)
open NumberedWindowInternalCoverCombinedRestrictedPairedMinimumTargets

attribute [local irreducible] programGraph

theorem exact_OpenCoverCombinedRestrictedPairedEdge : ExactOpenCoverCombinedRestrictedPairedEdge := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m P W D X a b syn ty argument fg gf ma mb
  apply exact_OpenCoverCombinedRestrictedPairedCrossCover V TV M M0 B T base s body α Γ
    ctx dom cod f g arg m (edgeGraph X W ctx cod a b) syn ty argument fg gf ma mb
  intro β j Δ vertices keep _ edge
  simp only [edgeGraph,programRename,edgeTape,quadInputsRename,sucRelabel,zRelabel]
  simp only [edgeGraph,edgeTape] at edge
  exact edge

theorem exact_OpenCoverCombinedRestrictedPairedEdgeMinimum :
    ExactOpenCoverCombinedRestrictedPairedEdgeMinimum := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg x y P W X a b ab ba la lb
  obtain ⟨ab⟩ := ab
  obtain ⟨ba⟩ := ba
  obtain ⟨la⟩ := la
  obtain ⟨lb⟩ := lb
  obtain ⟨law⟩ := exact_MutualEdgeMinimumEquality P.cover s (thinPairedExchange (directedX base P.V)) W
    body α Γ ctx cod a b x y
  exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction
    (Derivation.conjunctionIntroduction la lb) (Derivation.conjunctionIntroduction ab ba))⟩

theorem exact_OpenCoverCombinedRestrictedPairedParentMinimum :
    ExactOpenCoverCombinedRestrictedPairedParentMinimum := by
  intro V TV M M0 B T base s body α Γ ctx dom cod f g arg m x y P W D X a b syn ty argument fg gf ma mb la lb
  have ab := exact_OpenCoverCombinedRestrictedPairedEdge V TV M M0 B T base s body α Γ
    ctx dom cod f g arg m syn ty argument fg gf ma mb
  have ba := exact_OpenCoverCombinedRestrictedPairedEdge V TV M M0 B T base s body α Γ
    ctx dom cod g f arg m syn ty argument gf fg mb ma
  exact exact_OpenCoverCombinedRestrictedPairedEdgeMinimum V TV M M0 B T base s body α Γ
    ctx dom cod f g arg x y ab ba la lb

#print axioms exact_OpenCoverCombinedRestrictedPairedEdge
#print axioms exact_OpenCoverCombinedRestrictedPairedEdgeMinimum
#print axioms exact_OpenCoverCombinedRestrictedPairedParentMinimum
end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedPairedMinimumProof
