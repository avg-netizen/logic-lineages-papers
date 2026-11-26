module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJEmptySpecializedProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldWithEmptyProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalAccessibilityRules
open ID1Completion.SourcePresentation (sourceBody)
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc)
open NumberedWindowInternalCertifiedUnionStepProof (Pr CertifiedOriginSplit)
open NumberedWindowInternalConsUnionReportBuildProof (Report)
open NumberedWindowInternalLiteralSparseJFoldSyntaxProof (LiteralScalarSingletonPromotion typedAt scalarMembers)
open NumberedWindowInternalLiteralSparseJFoldProof (exact_LiteralSparseParsedJFold)
open NumberedWindowInternalLiteralJEmptySpecializedProof (exact_LiteralSelectedEmptyJ)

/-- Actual selected symbolic J fold. Its empty case is now supplied by
the exact theorem in the very same literal-count body. -/
theorem exact_LiteralSparseParsedJFoldWithEmpty (i : Program 1) (r : Program 3) (c : Nat)
    (splitter : CertifiedOriginSplit (literalData i r) c permutation)
    (promote : LiteralScalarSingletonPromotion i r c)
    (α : Type) (Γ : List (Formula α)) (n s : OTerm α)
    (parsed : Report (B := sourceBody (literalData i r) c) (Γ := Γ) parser (suc s) ![n])
    (typed : Pr (literalData i r) c Γ (typedAt i s))
    (all : Pr (literalData i r) c Γ (scalarMembers s)) :
    Pr (literalData i r) c Γ (membership true n) :=
  exact_LiteralSparseParsedJFold i r c splitter (exact_LiteralSelectedEmptyJ i r c)
    promote α Γ n s parsed typed all

#print axioms exact_LiteralSparseParsedJFoldWithEmpty

end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSparseJFoldWithEmptyProof
