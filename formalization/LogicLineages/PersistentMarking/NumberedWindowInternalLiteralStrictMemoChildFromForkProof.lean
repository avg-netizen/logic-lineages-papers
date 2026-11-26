module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkFunctionAlignmentProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictForkRetapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictDualInversionForkProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicAddressReportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMemoChildFromForkProof
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
open NumberedWindowInternalLiteralStrictForkFunctionAlignmentProof (exact_OpenStrictForkFunctionAlignment)
open NumberedWindowInternalLiteralStrictMemoChildCasesProof (exact_OpenStrictMemoChildCases)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalNeutralFactsTargets (direct)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn rawWithTarget direct
variable {α : Type} {Γ : List (Formula α)}

/-- In the actual strict inversion fork, the child-step source is the
original function argument address, not merely a related newly chosen
representative. The lexical and finite type gates are all recovered
from the already accepted original application operands. -/
theorem exact_OpenStrictMemoChildFromFork (cv tv : Program 1) (C : Program 3) (Base : Program 4)
    (s : Settings) (base : Program 2) (T : Program 1) (raw : Program 5) (finite : List Nat) (c : Nat)
    (x u ctx result dom cod fn arg sc st before after cert q w r d e f a child g : OTerm α)
    (goal : Formula α) :
    let E := recursiveTypedMemo Base
    let W := strictSealedWindow C s base T
    let L₀ := packedLeastOn C E s
    let L := memoFilteredLeast C Base s
    let i := finiteScalar (addressScalar cv tv W L) finite
    let R := rawWithTarget i cv tv raw L
    let data := S i cv tv R L
    let B := sourceBody data c
    WindowEndpoints W E → Preserves E L₀ → MemoSelectedReports C s Base →
    D B Γ (unary i (suc z) x) → D B Γ (unary i (suc z) u) →
    D B Γ (parsedApplicationInputs x u ctx result dom cod fn arg) →
    D B Γ (eqn sc ctx) →
    D B Γ (programGraph L (suc before) ![sc,st,auxiliaryTerm dom cod fn arg]) →
    D B Γ (eqn q (auxiliaryTerm d e f a)) →
    D B Γ (programGraph raw (suc z) ![sc,rawCons d e,f,child,g]) →
    D B Γ (windowAt W sc (rawCons d e) g) →
    D B Γ (hopCalls R L sc st before cert after q w r) →
    (∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (gmin : OTerm β),
      (∀ p ∈ Γ, p.relabel j ∈ Δ) →
      D B Δ (leastOnGraph C E s (sc.relabel j) (rawCons (d.relabel j) (e.relabel j)) (g.relabel j) gmin) →
      D B Δ (unary i (suc z) (literalAddress (sc.relabel j) (rawCons (d.relabel j) (e.relabel j)) gmin)) →
      D B Δ (direct data (hop cv tv R L) c (x.relabel j)
        (literalAddress (sc.relabel j) (rawCons (d.relabel j) (e.relabel j)) gmin)) →
      D B Δ (goal.relabel j)) →
    D B Γ goal := by
  intro E W L₀ L i R data B ends stable selected left right parsed scCtx app qParts rawChild typed calls use
  obtain ⟨physical⟩ := calls
  have rawSource : D B Γ (programGraph L (suc before) ![sc,st,q]) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.conjunctionRight physical))⟩
  obtain ⟨cvSc,tvArr,listed,fnSc,sourceAddress⟩ :=
    exact_OpenStrictForkFunctionAlignment cv tv W L₀ finite x u ctx result dom cod fn arg sc st before q d e f a
      left right parsed scCtx app rawSource qParts
  refine exact_OpenStrictMemoChildCases cv tv C Base s base T raw finite c
    sc (rawCons d e) f child g fn goal ends stable selected cvSc tvArr listed typed rawChild fnSc ?_
  intro β j Δ k keep least check step
  rw [rawConsRename] at least check step
  have source := renameInto sourceAddress j Δ keep
  change D B Δ ((eqn x (addressTerm sc (rawCons d e) fn)).relabel j) at source
  rw [eqnRelabel,renameAddress,rawConsRename] at source
  obtain ⟨sEq⟩ := source
  let fAddress := literalAddress (sc.relabel j) (rawCons (d.relabel j) (e.relabel j)) (fn.relabel j)
  let dest := literalAddress (sc.relabel j) (rawCons (d.relabel j) (e.relabel j)) k
  have moved : D B Δ (direct data (hop cv tv R L) c (x.relabel j) dest) :=
    exact_OpenStrictRetapeDirectSource data (hop cv tv R L) c fAddress (x.relabel j) dest ⟨symm sEq⟩ step
  exact use β j Δ k keep least check moved

#print axioms exact_OpenStrictMemoChildFromFork
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMemoChildFromForkProof
