module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSealedWindowProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowParentProof
import LogicLineages.PersistentMarking.NumberedWindowInternalStrictAuxWindowResultTypeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverStrictAuxIntroduceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLeastCoverageProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedDomainSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionEqualityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictSealedWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalGraphCompositionEqualityProof (graphInputTransport)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePackedDomainTargets (hasLeast)
open NumberedWindowInternalSparsePackedDomainSyntaxProof (casesLeast)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalAuxWindowMemoTargets (IntrinsicWindowCalibrated)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow strictAuxChildren)
open NumberedWindowInternalStrictAuxWindowNumericProof (exact_StrictAuxWindowCalibration)
open NumberedWindowInternalStrictAuxWindowParentProof (exact_OpenStrictAuxWindowParent)
open NumberedWindowInternalStrictAuxWindowResultTypeProof (exact_OpenStrictAuxWindowResultType)
open NumberedWindowInternalCoverStrictAuxIntroduceProof (exact_OpenCoverStrictAuxIntroduce)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalLiteralLeastCoverageProof (exact_OpenCoverageFromLeast)
open NumberedWindowInternalLiteralSealedWindowProof (D sealedWindow exact_SealedWindowCalibration exact_OpenSealedWindow)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def strictSealedWindow (C : Program 3) (s : Settings) (base : Program 2) (T : Program 1) : Program 3 :=
  sealedWindow C s (strictAuxWindow base T)

theorem exact_StrictSealedWindowCalibration (C : Program 3) (s : Settings) (base : Program 2)
    (T : Program 1) (cover : ActualSelectedCoverOutput C) (seeds : WindowSeedsCovered s)
    (baseFit : IntrinsicWindowCalibrated s base) (fit : TypeGuardCalibrated s T) :
    ActualPackedWindow s (strictSealedWindow C s base T) :=
  exact_SealedWindowCalibration C s (strictAuxWindow base T) cover seeds
    (exact_StrictAuxWindowCalibration s base T baseFit fit)

theorem exact_OpenCoverageFromLeastDomain (C W : Program 3) (X : Program 2) (s : Settings)
    (ctx ty q : OTerm α) (held : D B Γ (hasLeast C X W s ctx ty q)) :
    D B Γ (coverageReport C s ctx q) := by
  apply casesLeast C X W s ctx ty q (coverageReport C s ctx q) held
  intro β j Δ selected keep known
  simp only [coverageReport,programRename,tripleInputsRename,sucRelabel,zRelabel]
  exact exact_OpenCoverageFromLeast C X W s (ctx.relabel j) (ty.relabel j)
    (q.relabel j) selected known

theorem strictWindowTypeMove (W : Program 3) (ctx ty found raw : OTerm α)
    (same : D B Γ (eqn ty found)) (held : D B Γ (windowAt W ctx ty raw)) :
    D B Γ (windowAt W ctx found raw) := by
  unfold windowAt programGraph at held ⊢
  apply graphInputTransport B α 3 Γ (OrdinaryArithmetic.graphFormula W)
    (suc z) ![ctx,ty,raw] ![ctx,found,raw] _ held
  intro j
  rw [onEquality]
  exact Fin.cases (⟨refl ctx⟩ : D B Γ (eqn ctx ctx)) (Fin.cases same
    (Fin.cases (⟨refl raw⟩ : D B Γ (eqn raw raw)) (fun v => Fin.elim0 v))) j

theorem exact_OpenStrictSealedAuxReports (C : Program 3) (s : Settings)
    (base : Program 2) (T : Program 1) (ctx ty dom cod fn arg : OTerm α)
    (parent : D B Γ (windowAt (strictSealedWindow C s base T) ctx ty (auxiliaryTerm dom cod fn arg))) :
    D B Γ (eqn ty cod) ∧ D B Γ (strictAuxChildren base T ctx dom cod fn arg) := by
  let U := strictAuxWindow base T
  let seed := auxiliaryTerm dom cod fn arg
  have upper := (exact_OpenSealedWindow C s U ctx ty seed).1 parent |>.1
  have codTy := exact_OpenStrictAuxWindowResultType base T B α Γ ctx ty dom cod fn arg upper
  have corrected := strictWindowTypeMove U ctx ty cod seed codTy upper
  exact ⟨codTy,exact_OpenStrictAuxWindowParent base T B α Γ ctx dom cod fn arg corrected⟩

/-- Unlike the earlier forming choice, a positive literal auxiliary
query in this window exposes both actual child windows and the type
of the raw parent. Existing child least domains pay their exact
cover predicates, so the SAME strict sealed window recurs. -/
theorem exact_OpenStrictSealedAuxChildren (C W : Program 3) (X : Program 2) (s : Settings)
    (base : Program 2) (T : Program 1) (ctx ty dom cod fn arg : OTerm α)
    (parent : D B Γ (windowAt (strictSealedWindow C s base T) ctx ty (auxiliaryTerm dom cod fn arg)))
    (fnDomain : D B Γ (hasLeast C X W s ctx (rawCons dom cod) fn))
    (argDomain : D B Γ (hasLeast C X W s ctx dom arg)) :
    D B Γ (eqn ty cod) ∧ D B Γ (unary T (suc z) dom) ∧ D B Γ (unary T (suc z) cod) ∧
    D B Γ (windowAt (strictSealedWindow C s base T) ctx (rawCons dom cod) fn) ∧
    D B Γ (windowAt (strictSealedWindow C s base T) ctx dom arg) := by
  let U := strictAuxWindow base T
  obtain ⟨codTy,⟨bits⟩⟩ := exact_OpenStrictSealedAuxReports C s base T ctx ty dom cod fn arg parent
  let types := Derivation.conjunctionLeft bits
  let wins := Derivation.conjunctionRight bits
  have fnCover := exact_OpenCoverageFromLeastDomain C W X s ctx (rawCons dom cod) fn fnDomain
  have aCover := exact_OpenCoverageFromLeastDomain C W X s ctx dom arg argDomain
  exact ⟨codTy,⟨Derivation.conjunctionLeft types⟩,⟨Derivation.conjunctionRight types⟩,
    (exact_OpenSealedWindow C s U ctx (rawCons dom cod) fn).2 ⟨Derivation.conjunctionLeft wins⟩ fnCover,
    (exact_OpenSealedWindow C s U ctx dom arg).2 ⟨Derivation.conjunctionRight wins⟩ aCover⟩

/-- The same physical window also admits exact synthesis on a known
auxiliary whose two children and original type guards are genuine. -/
theorem exact_OpenStrictSealedAuxParent (C : Program 3) (s : Settings) (base : Program 2) (T : Program 1)
    (ctx dom cod fn arg : OTerm α)
    (d : D B Γ (unary T (suc z) dom)) (c : D B Γ (unary T (suc z) cod))
    (f : D B Γ (windowAt (strictSealedWindow C s base T) ctx (rawCons dom cod) fn))
    (a : D B Γ (windowAt (strictSealedWindow C s base T) ctx dom arg))
    (cover : D B Γ (coverageReport C s ctx (auxiliaryTerm dom cod fn arg))) :
    D B Γ (windowAt (strictSealedWindow C s base T) ctx cod (auxiliaryTerm dom cod fn arg)) := by
  let U := strictAuxWindow base T
  let seed := auxiliaryTerm dom cod fn arg
  obtain ⟨fnOK⟩ := (exact_OpenSealedWindow C s U ctx (rawCons dom cod) fn).1 f |>.1
  obtain ⟨argOK⟩ := (exact_OpenSealedWindow C s U ctx dom arg).1 a |>.1
  obtain ⟨dOK⟩ := d
  obtain ⟨cOK⟩ := c
  have parent := exact_OpenCoverStrictAuxIntroduce base T B α Γ ctx dom cod fn arg
    ⟨Derivation.conjunctionIntroduction (Derivation.conjunctionIntroduction dOK cOK)
      (Derivation.conjunctionIntroduction fnOK argOK)⟩
  exact (exact_OpenSealedWindow C s U ctx cod seed).2 parent cover

#print axioms strictWindowTypeMove
#print axioms exact_OpenStrictSealedAuxReports
#print axioms exact_StrictSealedWindowCalibration
#print axioms exact_OpenCoverageFromLeastDomain
#print axioms exact_OpenStrictSealedAuxChildren
#print axioms exact_OpenStrictSealedAuxParent
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictSealedWindowProof
