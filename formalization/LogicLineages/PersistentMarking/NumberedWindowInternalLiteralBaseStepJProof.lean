module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepScalarProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCertifiedTargetTypedProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepJProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalCertifiedUnionStepProof (Pr)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (typedAt scalarMembers)
open NumberedWindowInternalLiteralBaseStepScalarProof (exact_OpenLiteralBaseStepScalarMembers)
open NumberedWindowInternalLiteralCertifiedTargetTypedProof (exact_OriginalLiteralCertifiedTargetTyped)
open NumberedWindowInternalLiteralJCompleteProof (exact_LiteralParsedJ)

/-- A genuine installed base or extra replacement preserves the complete
typed local scalar-member family and produces J of the known actual raw
target. The original certificate itself pays target typing. -/
theorem exact_LiteralCertifiedBaseStepJ (i : Program 1) (r : Program 3) (c : Nat)
    {α : Type} {Γ : List (Formula α)}
    (source target witness ds dt : OTerm α)
    (cert : Pr (literalData i r) c Γ (certificate (literalData i r) true c source target witness))
    (pS : Pr (literalData i r) c Γ (unary parser (suc ds) source))
    (pT : Pr (literalData i r) c Γ (unary parser (suc dt) target))
    (members : Pr (literalData i r) c Γ (scalarMembers ds)) :
    Pr (literalData i r) c Γ (membership true target) := by
  have all := exact_OpenLiteralBaseStepScalarMembers i r c α Γ source target witness ds dt cert pS pT members
  have typed : Pr (literalData i r) c Γ (typedAt i dt) :=
    exact_OriginalLiteralCertifiedTargetTyped i r c source target witness dt cert pT
  exact exact_LiteralParsedJ i r c α Γ target dt (by simpa only [unary] using pT) typed all

#print axioms exact_LiteralCertifiedBaseStepJ
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBaseStepJProof
