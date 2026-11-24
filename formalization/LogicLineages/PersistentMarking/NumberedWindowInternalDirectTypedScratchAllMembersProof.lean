module

public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchMemberProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalListInduction (atCode atIndex constructorBody constructors premises)
open ID1Completion.InternalListInductionProof (actualOriginalListInductionAtCode)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalAdditionLawsProof (impSubst)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb bindEmbedding liftBind varBind sucRelabel zRelabel sucSubst zSubst)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePathSuccessfulAdvanceGraphSyntaxProof (unarySubst)
open NumberedWindowInternalSparsePassWindowSyntaxProof (memberSubst)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenMemberConsProof (headMember tailMember)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectTypedScratchMemberTargets (fromMember)
open NumberedWindowInternalDirectTypedScratchMemberProof (exact_TypedScratchMember)
open NumberedWindowInternalDirectTypedScratchIntroProof (exact_TypedScratchNil exact_IntroTypedScratchCons)
open NumberedWindowInternalDirectTypedScratchAllMembersTargets
open NumberedWindowInternalDirectTypedScratchAllMembersSyntaxProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atNeedle (i : Program 1) (code key : OTerm α)
    (all : Nonempty (Derivation B Γ (allMembers i code)))
    (present : Nonempty (Derivation B Γ (memberGraph code key))) :
    Nonempty (Derivation B Γ (unary i (suc z) key)) := by
  obtain ⟨all⟩ := all
  obtain ⟨present⟩ := present
  have chosen := Derivation.universalElimination (emb key) all
  have law : Derivation B Γ ((memberGraph code key).imp (unary i (suc z) key)) := by
    simpa only [allMembers,instantiate,bindEmbedding,impSubst,memberSubst,unarySubst,
      sucSubst,zSubst,liftBind,varBind] using chosen
  exact ⟨Derivation.implicationElimination law present⟩

/-- Build the object quantifier itself from prior pointwise induction. -/
private theorem quantify (i : Program 1) (code : OTerm α)
    (typed : Nonempty (Derivation B Γ (unary (typedScratch i) (suc z) code))) :
    Nonempty (Derivation B Γ (allMembers i code)) := by
  let ρ : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := memberGraph (code.relabel ρ) key
  let Δ := H :: Γ.map (fun f => f.relabel ρ)
  have keep : ∀ f ∈ Γ, f.relabel ρ ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have th : Nonempty (Derivation B Δ (unary (typedScratch i) (suc z) (code.relabel ρ))) := by
    simpa only [unaryRename,sucRelabel,zRelabel] using renameInto typed ρ Δ keep
  obtain ⟨held⟩ := th
  obtain ⟨rule⟩ := exact_TypedScratchMember i B (α ⊕ Fin 1) Δ (code.relabel ρ) key
  change Derivation B Δ ((unary (typedScratch i) (suc z) (code.relabel ρ) ⊓ H).imp
    (unary i (suc z) key)) at rule
  have result := Derivation.implicationElimination rule
    (Derivation.conjunctionIntroduction held (Derivation.hypothesis List.mem_cons_self))
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction result)⟩

private theorem tailQuantifier (i : Program 1) (code head tail : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (all : Nonempty (Derivation B Γ (allMembers i code))) :
    Nonempty (Derivation B Γ (allMembers i tail)) := by
  let ρ : α → α ⊕ Fin 1 := Sum.inl
  let key : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let H := memberGraph (tail.relabel ρ) key
  let Δ := H :: Γ.map (fun f => f.relabel ρ)
  have keep : ∀ f ∈ Γ, f.relabel ρ ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have realCell : Nonempty (Derivation B Δ (consGraph (code.relabel ρ) (head.relabel ρ) (tail.relabel ρ))) := by
    simpa only [consGraphRename] using renameInto cell ρ Δ keep
  have hCode : Nonempty (Derivation B Δ (allMembers i (code.relabel ρ))) := by
    simpa only [allMembersRename] using renameInto all ρ Δ keep
  have mem := tailMember (code.relabel ρ) (head.relabel ρ) (tail.relabel ρ) key
    realCell ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨scalar⟩ := atNeedle i (code.relabel ρ) key hCode mem
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction scalar)⟩

private theorem consLaw (i : Program 1) (code head tail : OTerm α)
    (cell : Nonempty (Derivation B Γ (consGraph code head tail)))
    (below : Nonempty (Derivation B Γ (fromAllMembers i tail))) :
    Nonempty (Derivation B Γ (fromAllMembers i code)) := by
  let P := allMembers i code
  have assumed : Nonempty (Derivation B (P :: Γ) (allMembers i code)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨cell⟩ := cell
  obtain ⟨above⟩ := below
  let held : Nonempty (Derivation B (P :: Γ) (consGraph code head tail)) := ⟨addHyp cell P⟩
  have atHead := headMember code head tail head held ⟨refl head⟩
  have typedHead := atNeedle i code head assumed atHead
  obtain ⟨universalTail⟩ := tailQuantifier i code head tail held assumed
  have typedTail : Derivation B (P :: Γ) (unary (typedScratch i) (suc z) tail) :=
    Derivation.implicationElimination (addHyp above P) universalTail
  obtain ⟨typed⟩ := exact_IntroTypedScratchCons i B α (P :: Γ) code head tail held typedHead ⟨typedTail⟩
  exact ⟨Derivation.implicationIntroduction typed⟩

private theorem constructorLaw (i : Program 1) :
    Nonempty (Derivation B Γ (constructors (invariant i))) := by
  apply actualFiniteUniversalIntroduction B α 3 Γ (constructorBody (invariant i))
  let ρ : α → α ⊕ Fin 3 := Sum.inl
  let n : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let C := consGraph n h t
  let R := fromAllMembers i t
  let Δ := R :: C :: Γ.map (fun f => f.relabel ρ)
  change Nonempty (Derivation B (Γ.map (fun f => f.relabel ρ))
    (C.imp ((atIndex (invariant i) 2).imp (atIndex (invariant i) 0))))
  simp only [invariantIndex]
  obtain ⟨out⟩ := consLaw (B := B) (Γ := Δ) i n h t
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction out)⟩

theorem exact_TypedScratchAllMembers : ExactTypedScratchAllMembers := by
  intro i B α Γ code
  let T := unary (typedScratch i) (suc z) code
  obtain ⟨fromTyped⟩ := quantify (B := B) (Γ := T :: Γ) i code ⟨Derivation.hypothesis List.mem_cons_self⟩
  have base : Nonempty (Derivation B Γ (atCode (invariant i) z)) := by
    rw [invariantCode]
    obtain ⟨typed⟩ := exact_TypedScratchNil i B α (allMembers i (z : OTerm α) :: Γ)
    exact ⟨Derivation.implicationIntroduction typed⟩
  obtain ⟨start⟩ := base
  obtain ⟨step⟩ := constructorLaw (B := B) (α := α) (Γ := Γ) i
  have all : Nonempty (Derivation B Γ (premises (invariant i))) :=
    ⟨Derivation.conjunctionIntroduction start step⟩
  have converse := actualOriginalListInductionAtCode B α Γ (invariant i) code all
  rw [invariantCode] at converse
  obtain ⟨fromAll⟩ := converse
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction fromTyped) fromAll⟩

#print axioms exact_TypedScratchAllMembers
end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTypedScratchAllMembersProof
