module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratumTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCompleteProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratum
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (membership)
open ID1Completion.InternalStrongInduction (schema)
open ID1Completion.InternalStrongInductionProof (actualStrongInductionSchema)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.SourcePresentation (sourceBody)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalLiteralJCompleteProof (exact_LiteralParsedJ)
open NumberedWindowInternalConstructorLabelStratumTargets

private theorem labelAssembly {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (finite : FiniteMatrix α) (ordinary : OrdinaryMatrix α)
    (fin : Nonempty (Derivation B Γ (finiteProgress finite)))
    (ω : Nonempty (Derivation B Γ (ordinaryProgress finite ordinary))) :
    Nonempty (Derivation B Γ (labelStratum finite ordinary)) := by
  obtain ⟨ind⟩ := actualStrongInductionSchema B α (finiteLabelBody finite)
  obtain ⟨progress⟩ := fin
  obtain ⟨finish⟩ := ω
  let lift : Derivation B Γ (schema (finiteLabelBody finite)) := weakenClosed ind Γ
  have finiteAll : Derivation B Γ (finiteLabels finite) :=
    Derivation.implicationElimination lift progress
  have ordinaryAll : Derivation B Γ (ordinaryLabel ordinary) :=
    Derivation.implicationElimination finish finiteAll
  exact ⟨Derivation.conjunctionIntroduction finiteAll ordinaryAll⟩

theorem exact_LabelStratumAtJBase : ExactLabelStratumAtJBase := by
  intro i r c α Γ base finite ordinary baseJ fin omega
  obtain ⟨held⟩ := baseJ
  obtain ⟨complete⟩ := labelAssembly finite ordinary fin omega
  exact ⟨Derivation.implicationElimination (Derivation.implicationIntroduction complete) held⟩

theorem exact_LabelStratumFromParsedBase : ExactLabelStratumFromParsedBase := by
  intro i r c α Γ base scratch finite ordinary parsed typed members fin omega
  have baseJ := exact_LiteralParsedJ i r c α Γ base scratch parsed typed members
  exact exact_LabelStratumAtJBase i r c α Γ base finite ordinary baseJ fin omega

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorLabelStratum
