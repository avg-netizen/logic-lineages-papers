module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPermutedDirectEdgeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedListOpenProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCertifiedUnionProgressSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountEquivalenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoordinateChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJPermutationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier membership edge)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalCarrierExtraction actualOriginalSuccessorClosure)
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalControlGraphSupportProof (valueUnique headTransport)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalTagArithmeticSupportProof (cancelSuc)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalCertifiedUnionProgressSupportProof (oddIntroduction)
open NumberedWindowInternalDirectTypedScratchAllMembersTargets (allMembers)
open NumberedWindowInternalDirectTypedScratchAllMembersProof (exact_TypedScratchAllMembers)
open NumberedWindowInternalDirectTypedScratchMemberProof (exact_TypedScratchMember)
open NumberedWindowInternalDirectTypedListOpenProof (exact_OpenJRaw exact_IntroJRaw)
open NumberedWindowInternalLiteralCountEquivalenceProof (exact_LiteralMemberReverse)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalCoordinateChecks (exact_DomainRules)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralPermutedDirectSpliceProof (D compare)
open NumberedWindowInternalLiteralPermutedDirectEdgeProof (exact_LiteralPermutedDirectEdge)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)

attribute [local irreducible] programGraph

/-- The literal observer transports all scalar typing across actual
open decoded tapes. It does not identify their ordered encodings. -/
theorem exact_LiteralTypedScratchPermutation (i : Program 1) (B : Positive (Fin 1))
    (α : Type) (Γ : List (Formula α)) (a b : OTerm α)
    (ha : D B Γ (unary (typedScratch i) (suc z) a)) (same : D B Γ (compare a b)) :
    D B Γ (unary (typedScratch i) (suc z) b) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let A := memberGraph (b.relabel j) key
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  have keep (f : Formula α) (h : f ∈ Γ) : f.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have co := renamePair permutation (suc z) a b same j keep
  simp only [sucRelabel,zRelabel] at co
  have held := renameInto ha j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at held
  obtain ⟨rule⟩ := exact_TypedScratchMember i B _ Δ (a.relabel j) key
  obtain ⟨attr⟩ := held
  obtain ⟨belongs⟩ := exact_LiteralMemberReverse B _ Δ (a.relabel j) (b.relabel j) key co
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have paid := Derivation.implicationElimination rule (Derivation.conjunctionIntroduction attr belongs)
  have all : Derivation B Γ (allMembers i b) :=
    Derivation.universalIntroduction (Derivation.implicationIntroduction paid)
  obtain ⟨equiv⟩ := exact_TypedScratchAllMembers i B α Γ b
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight equiv) all⟩

private theorem withTyped (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (a b sa sb : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (membership true a) → D B Γ (unary parser (suc sa) a) →
    D B Γ (unary parser (suc sb) b) → D B Γ (unary (typedScratch i) (suc z) sa) →
    D B Γ (compare sa sb) → D B Γ (membership true b) := by
  dsimp only
  intro JA pa pb typed ca
  let S := literalData i r
  let B := sourceBody S c
  have tb := exact_LiteralTypedScratchPermutation i B α Γ sa sb typed ca
  have cb := (exact_DomainRules i (jRaw i) r (dCore i r permutation) true c B α Γ b).2
    (exact_IntroJRaw i B α Γ b sb ⟨pb,tb⟩)
  apply oddIntroduction S c Γ b cb
  intro β j Δ target keep step
  have hp := renameInto JA j Δ keep
  rw [membershipRename] at hp
  have p := renameInto typed j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel] at p
  have co := renamePair permutation (suc z) sa sb ca j keep
  simp only [sucRelabel,zRelabel] at co
  have oldStep := exact_LiteralPermutedDirectEdge i r c β Δ (a.relabel j) (b.relabel j) target
    (sa.relabel j) (sb.relabel j) (renameParser a sa pa j Δ keep) (renameParser b sb pb j Δ keep) p co step
  exact actualOriginalSuccessorClosure S true c β Δ (a.relabel j) target hp oldStep

/-- The actual internal J predicate is invariant under permutation of
a positively parsed raw multiset. The certified deletion/replacement
edge is replayed from the original representative to the same target.
No appeal to external accessibility or a functional ordered split. -/
theorem exact_LiteralJPermutation (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (a b sa sb : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (membership true a) → D B Γ (unary parser (suc sa) a) →
    D B Γ (unary parser (suc sb) b) → D B Γ (compare sa sb) → D B Γ (membership true b) := by
  dsimp only
  intro JA pa pb same
  let S := literalData i r
  let B := sourceBody S c
  have ca := actualOriginalCarrierExtraction S true c α Γ a JA
  have accepted := (exact_DomainRules i (jRaw i) r (dCore i r permutation) true c B α Γ a).1 ca
  apply exact_OpenJRaw i B α Γ a (membership true b) accepted
  intro β j Δ as keep reports
  rw [membershipRename]
  have ja := renameInto JA j Δ keep
  rw [membershipRename] at ja
  have aParse := renameParser a sa pa j Δ keep
  have bParse := renameParser b sb pb j Δ keep
  have observed := renamePair permutation (suc z) sa sb same j keep
  simp only [sucRelabel,zRelabel] at observed
  obtain ⟨eq⟩ := valueUnique parser (suc (sa.relabel j)) (suc as) ![a.relabel j] aParse reports.parsed
  have co := headTransport permutation (suc z) (sa.relabel j) as
    (Fin.cons (sb.relabel j) Fin.elim0) ⟨cancelSuc eq⟩ observed
  exact withTyped i r c β Δ (a.relabel j) (b.relabel j) as (sb.relabel j) ja
    reports.parsed bParse reports.typed co

#print axioms exact_LiteralTypedScratchPermutation
#print axioms exact_LiteralJPermutation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJPermutationProof
