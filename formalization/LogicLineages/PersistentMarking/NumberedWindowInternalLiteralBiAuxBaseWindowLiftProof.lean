module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxWindowLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAuxiliaryParentProfileProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof
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

open NumberedWindowInternalLiteralBiAuxWindowLiftProof
open NumberedWindowInternalLiteralStrictMeasuredEnrichedLiftProof (exact_OpenObserverSuiteBase)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)

abbrev biAuxBaseOn (s : Settings) (X : Program 2) (V TV baseM : Program 1) (W : Program 3) :=
  withObservers (edge4 (selectedBiAuxExchange s X V TV baseM) W) childGuardObservers

abbrev joinedBiAuxBase (s : Settings) (X base : Program 2) (T V TV baseM : Program 1) :=
  biAuxBaseOn s X V TV baseM (NumberedWindowInternalLiteralJoinedAuxiliaryWindowProof.joinedAuxiliaryWindow s base T V TV baseM)

/-- The additional original observer tests do not obstruct physical
auxiliary congruence. The function-head test reads the previous
accepted child (or the identical fixed function) at its exact raw code. -/
theorem exact_OpenBiAuxBaseWindowLift (s : Settings) (X : Program 2)
    (T V TV baseM : Program 1) (W : Program 3)
    (parent : AuxWindowAssembly s T TV (unitAuxSyntax V TV) W) (v : Bool) (ctx dom cod q r fixed : OTerm α)
    (types : ParentTypeEvidence s T TV B Γ dom cod)
    (arg : D B Γ (windowAt W ctx
      (varyingOperandType (!v) dom cod) fixed))
    (arc : D B Γ (acceptEdge (biAuxBaseOn s X V TV baseM W)
      ctx (varyingOperandType v dom cod) q r)) :
    D B Γ (acceptEdge (biAuxBaseOn s X V TV baseM W) ctx cod
      (varyAuxiliary v dom cod q fixed) (varyAuxiliary v dom cod r fixed)) := by
  let E := edge4 (selectedBiAuxExchange s X V TV baseM) W
  let E₀ := biAuxBaseOn s X V TV baseM W
  have before := exact_OpenObserverSuiteBase E childGuardObservers ctx (varyingOperandType v dom cod) q r arc
  have formed := exact_OpenBiAuxWindowLift s X T V TV baseM W parent v ctx dom cod q r fixed types arg before
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

#print axioms exact_OpenBiAuxBaseWindowLift
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof
