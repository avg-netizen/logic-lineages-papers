module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipBottomProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalComputabilityDownwardProof (edgeCases)
open ID1Completion.InternalAccessibilityRulesProof (actualOriginalAccessibilityIntroduction)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalPresentationTargets (data)
open NumberedWindowInternalAtomicRefinement (refined)
open NumberedWindowInternalAtomicRefinementObjectTargets (packedBottomTerm)
open NumberedWindowInternalAtomicRefinementObjectChecks (exact_OpenRefinedAtomicCertificate)
open NumberedWindowInternalAtomicMembershipSyntaxProof (moveBottom underSuccessor)

theorem bottomSuccessors (i j : Program 1) (r d : Program 3) (context : Nat)
    (α : Type) (Γ : List (Formula α)) (x c t : OTerm α) :
    let S := data i j (refined i r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (equal x (packedBottomTerm c t))) →
    Nonempty (Derivation B Γ (successors S false context x)) := by
  dsimp only
  intro shape
  let S := data i j (refined i r) d
  let B := sourceBody S context
  let β := α ⊕ Fin 1
  let lift : α → β := Sum.inl
  let y : OTerm β := .var (.inr 0)
  let x' := x.relabel lift
  let c' := c.relabel lift
  let t' := t.relabel lift
  let H := edge S false context x' y
  let Δ := H :: Γ.map weaken
  have hShape : Nonempty (Derivation B Δ (equal x' (packedBottomTerm c' t'))) :=
    moveBottom x c t lift (underSuccessor Γ H) shape
  have hEdge : Nonempty (Derivation B Δ (edge S false context x' y)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hMember : Nonempty (Derivation B Δ (membership false y)) := by
    apply edgeCases S context x' y (membership false y) hEdge
    intro γ ρ Ω w hΩ hw
    obtain ⟨bad⟩ := exact_OpenRefinedAtomicCertificate.2 i j r d context γ Ω
      (x'.relabel ρ) w (y.relabel ρ) (c'.relabel ρ) (t'.relabel ρ)
      (moveBottom x' c' t' ρ hΩ hShape) hw
    exact ⟨Derivation.explosion bad⟩
  obtain ⟨hMember⟩ := hMember
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction hMember)⟩

theorem bottomMember (i j : Program 1) (r d : Program 3) (context : Nat)
    (α : Type) (Γ : List (Formula α)) (x c t : OTerm α) :
    let S := data i j (refined i r) d
    let B := sourceBody S context
    Nonempty (Derivation B Γ (equal x (packedBottomTerm c t))) →
    Nonempty (Derivation B Γ (carrier S false context x)) →
    Nonempty (Derivation B Γ (membership false x)) := by
  dsimp only
  intro shape valid
  exact actualOriginalAccessibilityIntroduction (data i j (refined i r) d) false context α Γ x
    valid (bottomSuccessors i j r d context α Γ x c t shape)

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicMembershipBottomProof
