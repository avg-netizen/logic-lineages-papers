module
public import LogicLineages.PersistentMarking.NumberedWindowInternalConstructorBaseLabelTargets
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalConstructorBaseLabel
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalStrongInduction (schema)
open ID1Completion.InternalStrongInductionProof (actualStrongInductionSchema)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (emb)
open NumberedWindowInternalConstructorLabelStratumTargets
open NumberedWindowInternalConstructorBaseLabelTargets
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalOddProgressiveInductionProof
  (exact_ActualOriginalOddProgressiveInduction exact_OriginalOddLowerInstance)
open NumberedWindowInternalLiteralJCompleteProof (exact_LiteralParsedJ)

private theorem labelProgressClose {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
    (f : FiniteMatrix α) (o : OrdinaryMatrix α)
    (h : Nonempty (Derivation B Γ (finiteProgress f ⊓ ordinaryProgress f o))) :
    Nonempty (Derivation B Γ (labelStratum f o)) := by
  obtain ⟨ind⟩ := actualStrongInductionSchema B α (finiteLabelBody f)
  obtain ⟨p⟩ := h
  have lift : Derivation B Γ (schema (finiteLabelBody f)) := weakenClosed ind Γ
  have all : Derivation B Γ (finiteLabels f) :=
    Derivation.implicationElimination lift (Derivation.conjunctionLeft p)
  exact ⟨Derivation.conjunctionIntroduction all
    (Derivation.implicationElimination (Derivation.conjunctionRight p) all)⟩

/-- Instantiate original odd induction with the whole object label stratum,
not one label at a time. The local hypotheses are both proved object
formulas in the exact original current carrier and lower-base context. -/
theorem exact_BaseLabelAtJ : ExactBaseLabelAtJ := by
  intro i r c α Γ base finite ordinary held steps
  let data := literalData i r
  have ready : Nonempty (Derivation (ID1Completion.SourcePresentation.sourceBody data c)
      (baseContext i r c Γ finite ordinary) (baseLabelMotive finite ordinary)) :=
    labelProgressClose finite ordinary steps
  obtain ⟨q⟩ := exact_ActualOriginalOddProgressiveInduction data c α Γ
    (baseLabelMotive finite ordinary) base ready
  obtain ⟨j⟩ := held
  exact ⟨Derivation.implicationElimination q j⟩

theorem exact_BaseLabelAtParsed : ExactBaseLabelAtParsed := by
  intro i r c α Γ base scratch finite ordinary parsed typed members steps
  exact exact_BaseLabelAtJ i r c α Γ base finite ordinary
    (exact_LiteralParsedJ i r c α Γ base scratch parsed typed members) steps

theorem exact_CertifiedLowerBaseLabel : ExactCertifiedLowerBaseLabel := by
  intro i r c α Γ large small witness finite ordinary h cert
  exact exact_OriginalOddLowerInstance (literalData i r) c Γ large small
    (baseLabelMotive finite ordinary) h (edgeIntroduction cert)

end LogicLineages.PersistentMarking.NumberedWindowInternalConstructorBaseLabel
