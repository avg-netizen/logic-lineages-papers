module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldWithEmptyProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonTargetFoldProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSpecializedProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalCertifiedUnionStepProof (Pr CertifiedOriginSplit)
open NumberedWindowInternalScalarSingletonInductionProof (singletonJ)
open NumberedWindowInternalLiteralSingletonProgressProof (exact_LiteralSingletonPromotionFromFold)
open NumberedWindowInternalLiteralSingletonTargetFoldProof (exact_LiteralSingletonTargetFoldSupply)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (LiteralScalarSingletonPromotion typedAt scalarMembers)
open NumberedWindowInternalLiteralSparseJFoldWithEmptyProof (exact_LiteralSparseParsedJFoldWithEmpty)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalConsUnionReportBuildProof (Report)

/-- Actual arbitrary-open scalar singleton promotion inside this one body.
The conditional premise is the same genuine certified multiset origin
split needed by the already supplied local target fold. -/
theorem exact_LiteralScalarSingletonImplication (i : Program 1) (r : Program 3) (c : Nat)
    (splitter : CertifiedOriginSplit (literalData i r) c permutation)
    (α : Type) (Γ : List (Formula α)) (q : OTerm α) :
    Pr (literalData i r) c Γ ((membership false q).imp (singletonJ q)) :=
  exact_LiteralSingletonPromotionFromFold i r c
    (exact_LiteralSingletonTargetFoldSupply i r c splitter) α Γ q

theorem exact_LiteralScalarSingletonPromotion (i : Program 1) (r : Program 3) (c : Nat)
    (splitter : CertifiedOriginSplit (literalData i r) c permutation) :
    LiteralScalarSingletonPromotion i r c := by
  intro α Γ q even _
  obtain ⟨law⟩ := exact_LiteralScalarSingletonImplication i r c splitter α Γ q
  obtain ⟨proof⟩ := even
  exact ⟨Derivation.implicationElimination law proof⟩

/-- Symbolic parsed raw list with actual local scalar I for each member.
No caller-supplied singleton promotion, count, carrier or empty-J premise. -/
theorem exact_LiteralParsedScalarMembersJ (i : Program 1) (r : Program 3) (c : Nat)
    (splitter : CertifiedOriginSplit (literalData i r) c permutation)
    (α : Type) (Γ : List (Formula α)) (raw scratch : OTerm α)
    (parsed : Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc scratch) ![raw])
    (typed : Pr (literalData i r) c Γ (typedAt i scratch))
    (members : Pr (literalData i r) c Γ (scalarMembers scratch)) :
    Pr (literalData i r) c Γ (membership true raw) :=
  exact_LiteralSparseParsedJFoldWithEmpty i r c splitter
    (exact_LiteralScalarSingletonPromotion i r c splitter) α Γ raw scratch parsed typed members

#print axioms exact_LiteralScalarSingletonImplication
#print axioms exact_LiteralScalarSingletonPromotion
#print axioms exact_LiteralParsedScalarMembersJ
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSingletonProgressSpecializedProof
