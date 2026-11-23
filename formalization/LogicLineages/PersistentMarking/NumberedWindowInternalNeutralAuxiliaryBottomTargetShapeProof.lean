module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeReadProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSourcePartitionRawGraphProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename moveReport)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast)
open NumberedWindowInternalAtomicRefinementObjectTargets (sourceFields)
open NumberedWindowInternalAuxBottomRefinement (sourceFlag auxFunction)
open NumberedWindowInternalNeutralAuxiliaryRefinement (auxDom auxFnType)
open NumberedWindowInternalAuxBottomRefinementObjectTargets (packedAuxBottomTerm)
open NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeReadProof (readHeld)
open NumberedWindowInternalDirectSourcePartitionRawGraphProof (keepThrough)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Continue at the actual selected target right argument, not the held
right argument of the source. No scalar-positive assertion is used. -/
theorem exact_OpenNeutralBottomAuxTargetShapeCases
    (y c dom cod stored : OTerm α) (goal : Formula α)
    (flags : Nonempty (Derivation B Γ
      (unary sourceFlag (suc z) y ⊓
        (sourceFields y c cod ⊓ (unary auxDom dom y ⊓ unary auxFnType stored y)))))
    (next : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (arg : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (equal (y.relabel j)
        (packedAuxBottomTerm (c.relabel j) (dom.relabel j) (cod.relabel j) (stored.relabel j) arg))) →
      Nonempty (Derivation B Δ (goal.relabel j))) :
    Nonempty (Derivation B Γ goal) := by
  apply programCases rawLeast ![y] goal
  intro β j Δ least keep leastReport
  rw [inputsRename] at leastReport
  apply programCases auxFunction ![y.relabel j] (goal.relabel j)
  intro γ k Ω fn keep' fnReport
  rw [inputsRename] at fnReport
  apply programCases (field 3) ![least.relabel k] ((goal.relabel j).relabel k)
  intro δ m Ω' arg keep'' argReport
  rw [inputsRename] at argReport
  let jk := k ∘ j
  let ρ := m ∘ jk
  have kept := keepThrough jk m (keepThrough j k keep keep') keep''
  rw [formulaRelabelComposition,formulaRelabelComposition]
  apply next δ ρ Ω' arg kept
  have a := moveReport (m ∘ k) Ω' (keepThrough k m keep' keep'') rawLeast least
    (y.relabel j) leastReport
  have b := moveReport m Ω' keep'' auxFunction fn ((y.relabel j).relabel k) fnReport
  obtain ⟨f⟩ := flags
  let pair := Derivation.conjunctionLeft (Derivation.conjunctionRight f)
  let types := Derivation.conjunctionRight (Derivation.conjunctionRight f)
  obtain ⟨f'⟩ := moveReport ρ Ω' kept sourceFlag (suc z) y ⟨Derivation.conjunctionLeft f⟩
  obtain ⟨c'⟩ := moveReport ρ Ω' kept rawContext c y ⟨Derivation.conjunctionLeft pair⟩
  obtain ⟨e'⟩ := moveReport ρ Ω' kept rawResult cod y ⟨Derivation.conjunctionRight pair⟩
  obtain ⟨d'⟩ := moveReport ρ Ω' kept auxDom dom y ⟨Derivation.conjunctionLeft types⟩
  obtain ⟨t'⟩ := moveReport ρ Ω' kept auxFnType stored y ⟨Derivation.conjunctionRight types⟩
  simp only [sucRelabel,zRelabel] at f'
  apply readHeld (y.relabel ρ) (c.relabel ρ) (dom.relabel ρ) (cod.relabel ρ) (stored.relabel ρ)
    (least.relabel (m ∘ k)) (fn.relabel m) arg
  · exact ⟨Derivation.conjunctionIntroduction f'
      (Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction c' e')
        (Derivation.conjunctionIntroduction d' t'))⟩
  · have assoc : (m ∘ k) ∘ j = m ∘ (k ∘ j) := rfl
    simpa only [ρ,jk,Term.relabel_relabel,assoc] using a
  · simpa only [ρ,jk,Term.relabel_relabel] using b
  · simpa only [Term.relabel_relabel,unary] using argReport

#print axioms exact_OpenNeutralBottomAuxTargetShapeCases
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralAuxiliaryBottomTargetShapeProof
