module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryParentProfileProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons unary)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseFieldCell (cellHead)
open NumberedWindowInternalSparseDirectedSeen (acceptEdge)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D exact_OpenEnrichedEdgeBase)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (edgeRename)
open NumberedWindowInternalLiteralEdgeObserversProof (withObservers exact_OpenInstalledObserver)
open NumberedWindowInternalLiteralChildGuardEdgeProof (childGuardObservers)
open NumberedWindowInternalLiteralAuxProfileObserversProof
open NumberedWindowInternalLiteralAuxiliaryParentProfileProof
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof (varyAuxiliary)
open NumberedWindowInternalLiteralMemoVaryingParentProof (varyingOperandType)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

abbrev selectedBiAuxBase (s : Settings) (X base : Program 2) (T V TV baseM : Program 1) :=
  withObservers (selectedBiAuxPlain s X base T V TV baseM) childGuardObservers

theorem exact_OpenObserverSuiteBase (E : Program 4) (ss : List (Program 3)) (ctx ty q r : OTerm α)
    (h : D B Γ (acceptEdge (withObservers E ss) ctx ty q r)) :
    D B Γ (acceptEdge E ctx ty q r) := by
  induction ss with
  | nil => exact h
  | cons a more ih => exact ih (exact_OpenEnrichedEdgeBase (withObservers E more) a ctx ty q r h)

/-- The additional original observer tests do not obstruct physical
auxiliary congruence. The function-head test reads the previous
accepted child (or the identical fixed function) at its exact raw code. -/
theorem exact_OpenStrictMeasuredBaseLift (s : Settings) (X base : Program 2)
    (T V TV baseM : Program 1) (v : Bool) (ctx dom cod q r fixed : OTerm α)
    (types : ParentTypeEvidence s T TV B Γ dom cod)
    (arg : D B Γ (windowAt (selectedBiAuxWindow s base T V TV baseM) ctx
      (varyingOperandType (!v) dom cod) fixed))
    (arc : D B Γ (acceptEdge (selectedBiAuxBase s X base T V TV baseM)
      ctx (varyingOperandType v dom cod) q r)) :
    D B Γ (acceptEdge (selectedBiAuxBase s X base T V TV baseM) ctx cod
      (varyAuxiliary v dom cod q fixed) (varyAuxiliary v dom cod r fixed)) := by
  let E := selectedBiAuxPlain s X base T V TV baseM
  let E₀ := selectedBiAuxBase s X base T V TV baseM
  have before := exact_OpenObserverSuiteBase E childGuardObservers ctx (varyingOperandType v dom cod) q r arc
  have formed := exact_OpenStrictMeasuredPlainLift s X base T V TV baseM v ctx dom cod q r fixed types arg before
  cases v
  · change D B Γ (acceptEdge E₀ ctx cod (auxiliaryTerm dom cod q fixed) (auxiliaryTerm dom cod r fixed))
    apply programCases cellHead ![q] _
    intro β j Δ h keep fnHead
    simp only [edgeRename,auxiliaryRename]
    rw [unaryInputsRename] at fnHead
    have prev := renameInto arc j Δ keep
    simp only [varyingOperandType,Bool.false_eq_true,ite_false,edgeRename,rawConsRename] at prev
    have ready := renameInto formed j Δ keep
    simp only [varyAuxiliary,Bool.false_eq_true,ite_false,ite_true,edgeRename,auxiliaryRename] at ready
    let c := ctx.relabel j
    let d := dom.relabel j
    let k := cod.relabel j
    let a := q.relabel j
    let b := r.relabel j
    let p := fixed.relabel j
    have stable := exact_OpenInstalledObserver E childGuardObservers (unaryObserver cellHead) (by simp [childGuardObservers])
    have old := exact_OpenUnaryObserverIntro cellHead c (rawCons d k) a h fnHead
    have moved := stable B β Δ c (rawCons d k) a b h prev old
    have new := exact_OpenUnaryObserverElim cellHead c (rawCons d k) b h moved
    exact exact_OpenInstallObserverSuite E childGuardObservers c k
      (auxiliaryTerm d k a p) (auxiliaryTerm d k b p) ready
      (exact_OpenAuxiliaryParentProfile c k d k a b p p h fnHead new)
  · change D B Γ (acceptEdge E₀ ctx cod (auxiliaryTerm dom cod fixed q) (auxiliaryTerm dom cod fixed r))
    apply programCases cellHead ![fixed] _
    intro β j Δ h keep fnHead
    simp only [edgeRename,auxiliaryRename]
    rw [unaryInputsRename] at fnHead
    have ready := renameInto formed j Δ keep
    simp only [varyAuxiliary,Bool.false_eq_true,ite_false,ite_true,edgeRename,auxiliaryRename] at ready
    let c := ctx.relabel j
    let d := dom.relabel j
    let k := cod.relabel j
    let a := q.relabel j
    let b := r.relabel j
    let p := fixed.relabel j
    exact exact_OpenInstallObserverSuite E childGuardObservers c k
      (auxiliaryTerm d k p a) (auxiliaryTerm d k p b) ready
      (exact_OpenAuxiliaryParentProfile c k d k p p a b h fnHead fnHead)

#print axioms exact_OpenObserverSuiteBase
#print axioms exact_OpenStrictMeasuredBaseLift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof
