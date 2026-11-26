module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersProof
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOriginChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalScratchAppendOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalScratchAppendOpenTargets (appendGraph appears)
open NumberedWindowInternalScratchAppendOpenSyntaxProof (appendRename)
open NumberedWindowInternalScratchAppendOriginChecks (exact_OpenScratchAppendOrigin)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectTypedScratchMemberProof (exact_TypedScratchMember)
open NumberedWindowInternalDirectTypedScratchAllMembersTargets (allMembers)
open NumberedWindowInternalDirectTypedScratchAllMembersProof (exact_TypedScratchAllMembers)
open NumberedWindowInternalDirectTypedUnionScratchTargets

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem side (i : Program 1) (code key : OTerm α)
    (typed : Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) code))) :
    Nonempty (Derivation B Γ ((memberGraph code key).imp (unary i (suc z) key))) := by
  let H := memberGraph code key
  obtain ⟨held⟩ := typed
  obtain ⟨rule⟩ := exact_TypedScratchMember i B α (H :: Γ) code key
  have pair : Derivation B (H :: Γ) (unary (typedScratch i) (suc z) code ⊓ H) :=
    Derivation.conjunctionIntroduction (addHyp held H) (Derivation.hypothesis List.mem_cons_self)
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination rule pair)⟩

theorem exact_TypedUnionScratch : ExactTypedUnionScratch := by
  intro i count B α Γ left right lhs joined support leftTyped rightTyped appendHeld observed
  let ρ : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := memberGraph (lhs.relabel ρ) key
  let Δ := H :: Γ.map (fun p => p.relabel ρ)
  have keep : ∀ p ∈ Γ, p.relabel ρ ∈ Δ := by
    intro p hp
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have le : Nonempty (Derivation B Δ (unary (typedScratch i) (suc z) (left.relabel ρ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto leftTyped ρ Δ keep
  have ri : Nonempty (Derivation B Δ (unary (typedScratch i) (suc z) (right.relabel ρ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto rightTyped ρ Δ keep
  have appended : Nonempty (Derivation B Δ (appendGraph (joined.relabel ρ) (left.relabel ρ) (right.relabel ρ))) := by
    simpa only [appendRename] using renameInto appendHeld ρ Δ keep
  have computed : Nonempty (Derivation B Δ (observer count (lhs.relabel ρ) (joined.relabel ρ))) := by
    simpa only [observer,programRename,binaryInputsRename,sucRelabel,zRelabel] using renameInto observed ρ Δ keep
  have memberJoined := support (α ⊕ Fin 1) Δ (lhs.relabel ρ) (joined.relabel ρ) key
    computed ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨either⟩ := exact_OpenScratchAppendOrigin B (α ⊕ Fin 1) Δ
    (left.relabel ρ) (right.relabel ρ) (joined.relabel ρ) key appended memberJoined
  obtain ⟨onLeft⟩ := side i (left.relabel ρ) key le
  obtain ⟨onRight⟩ := side i (right.relabel ρ) key ri
  have all : Derivation B Γ (allMembers i lhs) :=
    Derivation.universalIntroduction (Derivation.implicationIntroduction (disjunctionElimination either onLeft onRight))
  obtain ⟨law⟩ := exact_TypedScratchAllMembers i B α Γ lhs
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight law) all⟩

#print axioms exact_TypedUnionScratch
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedUnionScratchProof
