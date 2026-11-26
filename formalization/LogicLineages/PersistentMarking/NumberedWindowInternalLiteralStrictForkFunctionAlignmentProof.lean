module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkRetapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkFunctionAlignmentProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (headTransport)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontendTargets (parsedApplicationInputs)
open NumberedWindowInternalSparsePathSuccessfulAdvanceTargets (hopCalls)
open NumberedWindowInternalOriginalFirstHopCoreProof (literalAddress)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralAtomicAddressReportProof (renameAddress)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteScalar)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalLiteralStrictSealedWindowProof (strictSealedWindow)
open NumberedWindowInternalLiteralStrictOperandMinimaProof (exact_OpenStrictCertificateOperandMinima)
open NumberedWindowInternalLiteralStrictOperandGuardsProof (exact_OpenStrictFunctionOperandGuards)
open NumberedWindowInternalLiteralStrictForkRetapeProof
open NumberedWindowInternalLiteralStrictMemoChildCasesProof (exact_OpenStrictMemoChildCases)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (fullAuxiliaryDecorator childGuardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralTypeMembershipTargets (literalMembership)

/-- Original parent reports at the exact same selected value yield the
underlying function's physical least, at the original lexical scope and
arrow type required by the actual child reduction. -/
theorem exact_OpenStrictForkFunctionAlignment (cv tv : Program 1) (W L₀ : Program 3) (finite : List Nat)
    (x u ctx result dom cod fn arg sc st before q d e f a : OTerm α) :
    let L := guardedLeast (headerLeast (fullAuxiliaryDecorator L₀))
    let i := finiteScalar (addressScalar cv tv W L) finite
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg) →
    D B Γ (eqn sc ctx) →
    D B Γ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
    D B Γ (programGraph L (suc before) ![sc,st,q]) →
    D B Γ (eqn q (auxiliaryTerm d e f a)) →
    D B Γ (unary cv (suc z) sc) ∧ D B Γ (unary tv (suc z) (rawCons d e)) ∧
      D B Γ (literalMembership finite (rawCons d e)) ∧
      D B Γ (programGraph (childGuardedLeast L₀) (suc fn) ![sc,rawCons d e,f]) ∧
      D B Γ (eqn x (literalAddress sc (rawCons d e) fn)) := by
  intro L i left right parsed scCtx app rawSource qParts
  have app' := exact_OpenStrictRetapeContext L sc ctx st (auxiliaryTerm dom cod fn arg) (suc before) scCtx app
  have q' := exact_OpenStrictRetapeContext L sc ctx st q (suc before) scCtx rawSource
  obtain ⟨_,_,⟨domEq⟩,⟨codEq⟩,fnReport,_⟩ :=
    exact_OpenStrictCertificateOperandMinima cv tv W L₀ finite x u ctx st result dom cod fn arg q d e f a before
      left right parsed app' q' qParts
  have arr := exact_OpenStrictArrowRetape dom cod d e ⟨symm domEq⟩ ⟨symm codEq⟩
  obtain ⟨cv0,tv0,member⟩ := exact_OpenStrictFunctionOperandGuards cv tv W L finite
    x u ctx result dom cod fn arg left parsed
  obtain ⟨scEq⟩ := scCtx
  have cvSc : D B Γ (unary cv (suc z) sc) :=
    headTransport cv (suc z) ctx sc ![] ⟨symm scEq⟩ cv0
  have tvArr : D B Γ (unary tv (suc z) (rawCons d e)) :=
    headTransport tv (suc z) (rawCons dom cod) (rawCons d e) ![] arr tv0
  have listed := exact_OpenStrictMemberRetape finite (rawCons dom cod) (rawCons d e) arr member
  have fnSc := exact_OpenStrictRetapeContext (childGuardedLeast L₀) ctx sc (rawCons d e) f (suc fn) ⟨symm scEq⟩ fnReport
  have sourceAddress := exact_OpenStrictChildFunctionAddress x u ctx result dom cod fn arg sc d e parsed
    ⟨symm scEq⟩ arr
  exact ⟨cvSc,tvArr,listed,fnSc,sourceAddress⟩

#print axioms exact_OpenStrictForkFunctionAlignment
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkFunctionAlignmentProof
