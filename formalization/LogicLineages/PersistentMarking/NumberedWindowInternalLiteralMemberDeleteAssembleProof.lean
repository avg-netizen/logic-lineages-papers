module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJPermutationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSplitSideIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectInsertedIntroProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalScalarSingletonInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapLocalIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalRawConsUnionReportThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserThinOpenConsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountReflexiveProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAccessibilityRulesProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberDeleteAssembleProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (projectionValue compositionValue)
open ID1Completion.InternalRawListRecursionProof (nilValue consValue)
open ID1Completion.InternalListCodec (consCode)
open ID1Completion.InternalListCodecSupportProof (consGraph)
open ID1Completion.InternalApplicationValidityStackAppend (append appendStep)
open ID1Completion.InternalAccessibilityRules (edge)
open ID1Completion.InternalAccessibilityRulesProof (edgeIntroduction)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalLiteralPermutedDirectSpliceProof (D compare)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserThinOpenConsProof (exact_OriginalSparseParserNil)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalDirectBoundaryGuardsTargets (typedScratch)
open NumberedWindowInternalDirectInsertedScan (exactOpenScanNil)
open NumberedWindowInternalDirectInsertedIntroProof (exact_OriginalRawScanIntro)
open NumberedWindowInternalDirectTargetMapLocalIntroProof
  (exact_OpenTargetProjectionNil exact_OpenRawTargetProjectionIntro)
open NumberedWindowInternalDirectSplitSideIntroProof
  (OriginalChangedSide exact_LiteralChangedSideCertificate)
open NumberedWindowInternalLiteralCountReflexiveProof (exact_LiteralObserverReflexivity)
open NumberedWindowInternalScalarSingletonInductionProof (singletonCode)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A literal one-cell prefix appended to the actual residual gives
the same scratch cons produced by the checked erase/reinsertion proof. -/
theorem exact_AppendSingletonScratch (key single rest rebuilt : OTerm α)
    (one : D B Γ (consGraph single key z))
    (same : D B Γ (consGraph rebuilt key rest)) :
    D B Γ (programGraph append rebuilt ![single,rest]) := by
  have base : D B Γ (programGraph append rest ![z,rest]) :=
    nilValue (.projection 0) appendStep rest ![rest] (projectionValue 0 ![rest])
  let tape := (![key,rest,rest] : Fin 3 → OTerm α)
  have step : D B Γ (programGraph appendStep rebuilt tape) := by
    apply compositionValue consCode ![.projection 0,.projection 1] rebuilt tape ![key,rest] same
    intro k
    exact Fin.cases (projectionValue 0 tape)
      (Fin.cases (projectionValue 1 tape) (fun q => Fin.elim0 q)) k
  exact consValue (.projection 0) appendStep single key z rest rebuilt ![rest] one base step

/-- A retained actual member becomes a genuine strict singleton
successor when the other occurrences have a nonempty scratch residual.
Both original literal count tests use their actual ordered appends,
and the inserted list is genuinely empty. -/
theorem exact_LiteralMemberDeletionFromReports (i : Program 1) (r : Program 3) (c : Nat)
    (α : Type) (Γ : List (Formula α)) (raw key removed src one rest rebuilt dh dt : OTerm α) :
    let S := literalData i r
    let B := sourceBody S c
    D B Γ (unary parser (suc src) raw) →
    D B Γ (unary parser (suc one) (singletonCode key)) →
    D B Γ (unary parser (suc rest) removed) →
    D B Γ (unary (typedScratch i) (suc z) src) →
    D B Γ (unary (typedScratch i) (suc z) one) →
    D B Γ (consGraph one key z) → D B Γ (consGraph rebuilt key rest) →
    D B Γ (consGraph rest dh dt) → D B Γ (compare src rebuilt) →
    D B Γ (edge S true c raw (singletonCode key)) := by
  dsimp only
  intro parseSrc parseOne parseRest typedSrc typedOne single reinsert nonempty count
  let S := literalData i r
  let B := sourceBody S c
  have fields : OriginalChangedSide i r c Γ raw (singletonCode key) (singletonCode key) removed z
      src one one rest z rebuilt one dh dt :=
    ⟨⟨⟨parseSrc,parseOne,parseRest⟩,typedSrc,typedOne,nonempty⟩,parseOne,
      exact_OpenRawTargetProjectionIntro B α Γ z z z exact_OriginalSparseParserNil
        (exact_OpenTargetProjectionNil B α Γ),
      exact_AppendSingletonScratch key one rest rebuilt single reinsert,
      exact_AppendSingletonScratch key one z one single single,
      count,exact_LiteralObserverReflexivity B α Γ one,
      exact_OriginalRawScanIntro r z removed z exact_OriginalSparseParserNil
        (exactOpenScanNil r B α Γ removed)⟩
  exact edgeIntroduction (exact_LiteralChangedSideCertificate i r c raw (singletonCode key)
    (singletonCode key) removed z src one one rest z rebuilt one dh dt fields)

#print axioms exact_AppendSingletonScratch
#print axioms exact_LiteralMemberDeletionFromReports
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemberDeleteAssembleProof
