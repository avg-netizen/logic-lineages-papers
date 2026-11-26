module
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenQueryProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictCoreCurrentTableProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoRowSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowThinTableProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredAuxWindowIntroProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue successorValue programRename)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeAccept)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename rawConsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseFieldParser (scratchTable)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalAuxExchangeMemoStepTargets (currentKey unaryAfter)
open NumberedWindowInternalAuxExchangeMemoOpenStepCodeProof (unaryGraph)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph contextTable contextStep)
open NumberedWindowInternalAuxWindowOpenQueryProof (exact_OpenIntrinsicQuery)
open NumberedWindowInternalStrictAuxWindowThinTableProof (sameContext exact_OpenContextMemoSuccessor)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxUpdate)
open NumberedWindowInternalLiteralSyntaxMemoWindow (update syntaxAtKey)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalLiteralCoveredMemo
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralStrictCoreCurrentTableProof (exact_OpenStrictCoreAtCurrentTable)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
local notation "D" => Nonempty ∘ Derivation B Γ

def coveredAuxInputs (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (ctx dom cod fn arg : OTerm α) : Formula α :=
  (unary T (suc z) dom ⊓ unary T (suc z) cod) ⊓
    (windowGraph (coveredMemoWindow C s base T V) ctx (rawCons dom cod) fn ⊓
      windowGraph (coveredMemoWindow C s base T V) ctx dom arg)

private theorem introRow (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (ctx dom cod fn arg old : OTerm α)
    (children : D (coveredAuxInputs C s base T V ctx dom cod fn arg))
    (valid : D (unary V (suc z) (auxiliaryTerm dom cod fn arg)))
    (coverage : D (coverageReport C s ctx (auxiliaryTerm dom cod fn arg)))
    (table : D (contextTable (coveredUpdate C s base T V) old (memoPrior dom cod fn arg) ctx)) :
    D (contextStep (coveredUpdate C s base T V) (suc cod) (memoPrior dom cod fn arg) old ctx) := by
  let R := coveredUpdate C s base T V
  let prior := memoPrior dom cod fn arg
  let parent := auxiliaryTerm dom cod fn arg
  let xs : Fin 4 → OTerm α := ![prior,old,ctx,z]
  let verifier := conjunction contextPresent (ownSeed C s)
  have key : D (programGraph currentKey parent xs) :=
    unaryGraph .succ (.projection 0) parent prior xs (successorValue ![prior]) (projectionValue 0 xs)
  have covered : D (programGraph (coverageAtKey C s) (suc z) xs) := by
    apply compositionValue verifier ![.projection 2,constantZero 4,currentKey] (suc z) xs ![ctx,z,parent] coverage
    exact fun i => Fin.cases (projectionValue 2 xs)
      (Fin.cases (zeroConstantValue xs) (Fin.cases key (fun n => Fin.elim0 n))) i
  have Va : D (programGraph (syntaxAtKey V) (suc z) xs) := unaryGraph V currentKey (suc z) parent xs valid key
  have strict := exact_OpenStrictCoreAtCurrentTable base T R ctx dom cod fn arg old children table
  have syntaxPaid : D (programGraph (update base T V) (suc cod) xs) :=
    successorBranchIntro (normalize (syntaxAtKey V)) (constantZero 4) (strictAuxUpdate base T)
      (suc cod) z xs (normalizeAccept (syntaxAtKey V) xs Va) strict
  exact successorBranchIntro (normalize (coverageAtKey C s)) (constantZero 4) (update base T V)
    (suc cod) z xs (normalizeAccept (coverageAtKey C s) xs covered) syntaxPaid

/-- Introduce the actual enclosing covered auxiliary window from the
same enclosing child windows and the physical original coverage and
syntax checks. The strict head row reads the covered memo's own table. -/
theorem exact_OpenCoveredAuxWindowIntro (C : Program 3) (s : Settings) (base : Program 2) (T V : Program 1)
    (ctx dom cod fn arg : OTerm α)
    (children : D (coveredAuxInputs C s base T V ctx dom cod fn arg))
    (valid : D (unary V (suc z) (auxiliaryTerm dom cod fn arg)))
    (coverage : D (coverageReport C s ctx (auxiliaryTerm dom cod fn arg))) :
    D (windowGraph (coveredMemoWindow C s base T V) ctx cod (auxiliaryTerm dom cod fn arg)) := by
  let R := coveredUpdate C s base T V
  apply programCases (scratchTable (constantZero 2) R) ![memoPrior dom cod fn arg,ctx,z] _
  intro β j Δ old keep table
  simp only [tripleInputsRename,priorRename,zRelabel] at table
  simp only [windowGraph,programRename,tripleInputsRename,auxiliaryRename,sucRelabel,zRelabel]
  have a := renameInto children j Δ keep
  simp only [coveredAuxInputs,conjunctionRename,unaryRename,windowGraph,programRename,
    tripleInputsRename,sucRelabel,zRelabel,rawConsRename] at a
  have v := renameInto valid j Δ keep
  simp only [unaryRename,sucRelabel,zRelabel,auxiliaryRename] at v
  have c := renameInto coverage j Δ keep
  simp only [coverageReport,programRename,tripleInputsRename,sucRelabel,zRelabel,auxiliaryRename] at c
  let cc := ctx.relabel j
  let d := dom.relabel j
  let e := cod.relabel j
  let f := fn.relabel j
  let u := arg.relabel j
  have step := introRow C s base T V cc d e f u old a v c table
  have row := exact_OpenContextMemoSuccessor R B β Δ (suc e) (memoPrior d e f u) old cc table step
  let p := auxiliaryTerm d e f u
  have both := (sameContext R (suc e) cc p).mpr row
  exact (exact_OpenIntrinsicQuery (coveredIntrinsic C s base T V) B β Δ cc e p).mpr both

#print axioms exact_OpenCoveredAuxWindowIntro
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredAuxWindowIntroProof
