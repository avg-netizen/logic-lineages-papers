module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberProjectionProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralRawMembersJProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCharacterizationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier membership)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalCarrierExtraction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalPositiveEndpointRefinement (withEndpointCarriers)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (renameParser)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (scalarMembers)
open NumberedWindowInternalLiteralRawMembersJProof (allRawMembers exact_LiteralRawMembersJ)
open NumberedWindowInternalLiteralPermutedDirectSpliceProof (D)
open NumberedWindowInternalLiteralMemberProjectionProof (exact_LiteralJMemberSingleton)
open NumberedWindowInternalLiteralEndpointSingletonProof (exact_EndpointRefinedLiteralSingletonIff)

theorem exact_EndpointLiteralMemberJToI (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw src key : OTerm α) :
    let R := withEndpointCarriers i r
    let B := sourceBody (literalData i R) c
    D B Γ (membership true raw) → D B Γ (unary parser (suc src) raw) →
    D B Γ (memberGraph src key) → D B Γ (membership false key) := by
  dsimp only
  intro JA parse belongs
  exact (exact_EndpointRefinedLiteralSingletonIff i r c α Γ key).1
    (exact_LiteralJMemberSingleton i (withEndpointCarriers i r) c α Γ raw src key JA parse belongs)

/-- All actual decoded members of a held J code lie in I as one open
formula. This proof neither selects a particular external numeral nor
assembles separate instances by an omega rule. -/
theorem exact_EndpointLiteralJAllRawMembers (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw : OTerm α) :
    let B := sourceBody (literalData i (withEndpointCarriers i r)) c
    D B Γ (membership true raw) → D B Γ (allRawMembers raw) := by
  dsimp only
  intro JA
  let B := sourceBody (literalData i (withEndpointCarriers i r)) c
  let j : α → α ⊕ Fin 1 := Sum.inl
  let src : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let r₁ := raw.relabel j
  let A := unary parser (suc src) r₁
  let Δ : List (Formula (α ⊕ Fin 1)) := A :: Γ.map weaken
  let k : (α ⊕ Fin 1) → ((α ⊕ Fin 1) ⊕ Fin 1) := Sum.inl
  let key : OTerm ((α ⊕ Fin 1) ⊕ Fin 1) := .var (.inr 0)
  let M := memberGraph (src.relabel k) key
  let Ω : List (Formula ((α ⊕ Fin 1) ⊕ Fin 1)) := M :: Δ.map weaken
  have keep (p : Formula α) (h : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩)
  have more (p : Formula (α ⊕ Fin 1)) (h : p ∈ Δ) : p.relabel k ∈ Ω :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,h,rfl⟩)
  have J₁ := renameInto JA j Δ keep
  rw [membershipRename] at J₁
  have J₂ := renameInto J₁ k Ω more
  rw [membershipRename] at J₂
  have parsed : D B Δ A := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have next := renameParser r₁ src parsed k Ω more
  obtain ⟨scalar⟩ := exact_EndpointLiteralMemberJToI i r c _ Ω (r₁.relabel k) (src.relabel k)
    key J₂ next ⟨Derivation.hypothesis List.mem_cons_self⟩
  have each : Derivation B Δ (scalarMembers src) :=
    Derivation.universalIntroduction (Derivation.implicationIntroduction scalar)
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction each)⟩

/-- Exact raw-code criterion in the endpoint-guarded literal
presentation: J is equivalent to a held multiset carrier together
with the open statement that all actual decoded scalars belong to I. -/
theorem exact_EndpointLiteralJCharacterization (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw : OTerm α) :
    let R := withEndpointCarriers i r
    let S := literalData i R
    let B := sourceBody S c
    D B Γ (membership true raw) ↔ D B Γ (carrier S true c raw) ∧ D B Γ (allRawMembers raw) := by
  dsimp only
  constructor
  · intro held
    exact ⟨actualOriginalCarrierExtraction _ true c α Γ raw held,
      exact_EndpointLiteralJAllRawMembers i r c α Γ raw held⟩
  · rintro ⟨valid,each⟩
    exact exact_LiteralRawMembersJ i (withEndpointCarriers i r) c α Γ raw valid each

#print axioms exact_EndpointLiteralMemberJToI
#print axioms exact_EndpointLiteralJAllRawMembers
#print axioms exact_EndpointLiteralJCharacterization
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCharacterizationProof
