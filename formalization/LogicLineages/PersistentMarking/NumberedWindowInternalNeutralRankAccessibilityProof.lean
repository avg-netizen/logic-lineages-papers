module

public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeAlignmentSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankAccessibilityProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open SourceComputabilityFormulaSupportProof (allOne)
open ID1Completion.SourcePresentation (Data sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open ID1Completion.InternalStrongInduction (below lift)
open ID1Completion.InternalStrongInductionSyntaxProof (belowElimSyntax)
open ID1Completion.InternalStrongInductionProof (strongInduction)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalAccessibilityIntroduction)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalFreshProbeAlignmentSyntaxProof (carrierRename)
open NumberedWindowInternalAtomicMembershipSyntaxProof (membershipRename)
open NumberedWindowInternalNeutralRankTargets NumberedWindowInternalNeutralRankSyntaxProof

variable {S : Data} {g : Program 1} {c : Nat} {α : Type} {Γ : List (Formula α)}

private theorem useFamily (k x : OTerm α)
    (family : Nonempty (Derivation (sourceBody S c) Γ (rankFamily S g c k)))
    (cx : Nonempty (Derivation (sourceBody S c) Γ (carrier S false c x)))
    (rx : Nonempty (Derivation (sourceBody S c) Γ (positiveRank g k x))) :
    Nonempty (Derivation (sourceBody S c) Γ (membership false x)) := by
  obtain ⟨family⟩ := family
  obtain ⟨cx⟩ := cx
  obtain ⟨rx⟩ := rx
  have clause := Derivation.universalElimination (emb x) family
  rw [rankMatrixAt] at clause
  exact ⟨Derivation.implicationElimination clause (Derivation.conjunctionIntroduction cx rx)⟩

private theorem useLower (k j y : OTerm α)
    (earlier : Nonempty (Derivation (sourceBody S c) Γ (lowerRanks S g c k)))
    (strict : Nonempty (Derivation (sourceBody S c) Γ (ltF j k)))
    (cy : Nonempty (Derivation (sourceBody S c) Γ (carrier S false c y)))
    (ry : Nonempty (Derivation (sourceBody S c) Γ (positiveRank g j y))) :
    Nonempty (Derivation (sourceBody S c) Γ (membership false y)) := by
  obtain ⟨earlier⟩ := earlier
  obtain ⟨strict⟩ := strict
  have toRank := Derivation.universalElimination (emb j) earlier
  rw [belowElimSyntax,rankMotiveAt] at toRank
  exact useFamily j y ⟨Derivation.implicationElimination toRank strict⟩ cy ry

/-- The original accessibility introduction is used only after each
actual y on its unchanged edge has inherited the strict-rank proof. -/
theorem exact_OpenRankAccessibilityStep (drop : RankDrop S g c) (k x : OTerm α)
    (earlier : Nonempty (Derivation (sourceBody S c) Γ (lowerRanks S g c k)))
    (cx : Nonempty (Derivation (sourceBody S c) Γ (carrier S false c x)))
    (rx : Nonempty (Derivation (sourceBody S c) Γ (positiveRank g k x))) :
    Nonempty (Derivation (sourceBody S c) Γ (membership false x)) := by
  apply actualOriginalAccessibilityIntroduction S false c α Γ x cx
  let B := sourceBody S c
  let β := α ⊕ Fin 1
  let ρ : α → β := Sum.inl
  let y : OTerm β := .var (.inr 0)
  let A := edge S false c (x.relabel ρ) y
  let Δ := A :: Γ.map weaken
  have keep : ∀ f ∈ Γ, f.relabel ρ ∈ Δ :=
    fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have happened : Nonempty (Derivation B Δ A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have prior := renameInto earlier ρ Δ keep
  rw [lowerRanksRename] at prior
  have ranked := renameInto rx ρ Δ keep
  rw [positiveRankRename] at ranked
  have every : Nonempty (Derivation B Δ (membership false y)) := by
    apply drop β Δ (k.relabel ρ) (x.relabel ρ) y (membership false y) happened ranked
    intro γ j Ω l stays cy ry smaller
    have acceptable := renameInto prior j Ω stays
    rw [lowerRanksRename] at acceptable
    rw [membershipRename]
    exact useLower ((k.relabel ρ).relabel j) l (y.relabel j) acceptable smaller cy ry
  obtain ⟨every⟩ := every
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction every)⟩

/-- object course-of-values induction on the actual natural predecessor
rank k; the quantified raw x is chosen after the smaller-rank premise. -/
theorem exact_OpenRankAccessibilityAll (drop : RankDrop S g c) :
    Nonempty (Derivation (sourceBody S c) Γ (allOne (rankMotive S g c))) := by
  apply strongInduction (rankMotive S g c)
  let B := sourceBody S c
  let β := α ⊕ Fin 1
  let k : OTerm β := .var (.inr 0)
  let H : Formula β := below (lift (rankMotive S g c)) k
  let Δ : List (Formula β) := H :: Γ.map weaken
  let γ := β ⊕ Fin 1
  let ρ : β → γ := Sum.inl
  let x : OTerm γ := .var (.inr 0)
  let A := carrier S false c x ⊓ positiveRank g (k.relabel ρ) x
  let Ω : List (Formula γ) := A :: Δ.map weaken
  have keep : ∀ f ∈ Δ, f.relabel ρ ∈ Ω :=
    fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
  have smaller : Nonempty (Derivation B Δ (lowerRanks S g c k)) := by
    have h : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
    change Derivation B Δ (below (lift (rankMotive S g c)) k) at h
    rw [rankMotiveLift] at h
    exact ⟨h⟩
  have moved := renameInto smaller ρ Ω keep
  rw [lowerRanksRename] at moved
  have inputs : Derivation B Ω A := Derivation.hypothesis List.mem_cons_self
  obtain ⟨done⟩ := exact_OpenRankAccessibilityStep drop (k.relabel ρ) x moved
    ⟨Derivation.conjunctionLeft inputs⟩ ⟨Derivation.conjunctionRight inputs⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction done)⟩

/-- Only a genuine own carrier and positive unary rank graph are held.
The original strict path checker and its ID₁ body are not replaced. -/
theorem exact_OpenRankAccessibility (drop : RankDrop S g c) (k x : OTerm α)
    (cx : Nonempty (Derivation (sourceBody S c) Γ (carrier S false c x)))
    (rx : Nonempty (Derivation (sourceBody S c) Γ (positiveRank g k x))) :
    Nonempty (Derivation (sourceBody S c) Γ (membership false x)) := by
  obtain ⟨all⟩ := exact_OpenRankAccessibilityAll (α := α) (Γ := Γ) drop
  have family := Derivation.universalElimination (emb k) all
  rw [rankMotiveAt] at family
  exact useFamily k x ⟨family⟩ cx rx

#print axioms exact_OpenRankAccessibilityStep
#print axioms exact_OpenRankAccessibilityAll
#print axioms exact_OpenRankAccessibility
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankAccessibilityProof
