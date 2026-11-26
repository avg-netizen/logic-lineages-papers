module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredFormationInputsProof

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureParentTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedSelectedChildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureChildCasesProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureAlignProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredFormationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (rawCons)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax)
open NumberedWindowInternalCoverSelectedGrammarAuxScratchMeasuredTargets (MeasuredChild)
open NumberedWindowInternalChosenAuxMeasureParentTargets (AuxMeasureChild)
open NumberedWindowInternalChosenAuxMeasureChildCasesProof (exact_OpenChosenAuxMeasureChildCases)
open NumberedWindowInternalChosenAuxMeasureAlignProof (moveChild)
open NumberedWindowInternalMeasuredUnrestrictedSelectedScratchAuxiliaryWindowProof (moveMeasuredChild)
open NumberedWindowInternalMeasuredUnrestrictedSelectedFormationInputsProof
  (Inputs moveInputs)
open NumberedWindowInternalLiteralStrictMeasuredFormationInputsProof (exact_OpenStrictMeasuredFormationFromScopes)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictWindow)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalStrictAuxWindowTargets (strictAuxWindow)
open NumberedWindowInternalMeasuredUnrestrictedSelectedChildProof (exact_OpenUnrestrictedSelectedChildCases)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem withFunctionScope (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg mf df bf fState fTerms fArgs ma da ba : OTerm α)
    (held : Inputs s (measuredStrictWindow s base T V TV baseM) T TV B Γ ctx dom cod fn arg)
    (f : MeasuredChild baseM s B Γ mf df bf fState fTerms fArgs fn)
    (a : AuxMeasureChild baseM B Γ arg ma da ba) :
    Nonempty (Derivation B Γ (windowAt (measuredStrictWindow s base T V TV baseM) ctx cod (auxiliaryTerm dom cod fn arg))) := by
  let W := measuredStrictWindow s base T V TV baseM
  let goal := windowAt W ctx cod (auxiliaryTerm dom cod fn arg)
  apply exact_OpenUnrestrictedSelectedChildCases (unitAuxSyntax V TV) baseM s (strictAuxWindow base T)
    ctx dom arg ma da ba goal held.argument a
  intro β j Δ aState aTerms aArgs keep a'
  change Nonempty (Derivation B Δ ((windowAt W ctx cod (auxiliaryTerm dom cod fn arg)).relabel j))
  rw [windowRename,auxiliaryRename]
  have h := moveInputs s W T TV ctx dom cod fn arg j keep held
  have f' := moveMeasuredChild baseM s mf df bf fState fTerms fArgs fn j keep f
  exact exact_OpenStrictMeasuredFormationFromScopes s base T V TV baseM
    (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j) (arg.relabel j)
    (mf.relabel j) (df.relabel j) (bf.relabel j) (fState.relabel j) (fTerms.relabel j) (fArgs.relabel j)
    (ma.relabel j) (da.relabel j) (ba.relabel j) aState aTerms aArgs h f' a'

private theorem withMeasurements (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg mf df bf ma da ba : OTerm α)
    (held : Inputs s (measuredStrictWindow s base T V TV baseM) T TV B Γ ctx dom cod fn arg)
    (f : AuxMeasureChild baseM B Γ fn mf df bf)
    (a : AuxMeasureChild baseM B Γ arg ma da ba) :
    Nonempty (Derivation B Γ (windowAt (measuredStrictWindow s base T V TV baseM) ctx cod (auxiliaryTerm dom cod fn arg))) := by
  let W := measuredStrictWindow s base T V TV baseM
  let goal := windowAt W ctx cod (auxiliaryTerm dom cod fn arg)
  apply exact_OpenUnrestrictedSelectedChildCases (unitAuxSyntax V TV) baseM s (strictAuxWindow base T)
    ctx (rawCons dom cod) fn mf df bf goal held.function f
  intro β j Δ fState fTerms fArgs keep f'
  change Nonempty (Derivation B Δ ((windowAt W ctx cod (auxiliaryTerm dom cod fn arg)).relabel j))
  rw [windowRename,auxiliaryRename]
  have h := moveInputs s W T TV ctx dom cod fn arg j keep held
  have a' := moveChild baseM j Δ keep a
  exact withFunctionScope s base T V TV baseM (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) (mf.relabel j) (df.relabel j) (bf.relabel j) fState fTerms fArgs
    (ma.relabel j) (da.relabel j) (ba.relabel j) h f' a'

private theorem withFunctionMeasure (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg mf df bf : OTerm α)
    (held : Inputs s (measuredStrictWindow s base T V TV baseM) T TV B Γ ctx dom cod fn arg)
    (f : AuxMeasureChild baseM B Γ fn mf df bf) :
    Nonempty (Derivation B Γ (windowAt (measuredStrictWindow s base T V TV baseM) ctx cod (auxiliaryTerm dom cod fn arg))) := by
  let W := measuredStrictWindow s base T V TV baseM
  let goal := windowAt W ctx cod (auxiliaryTerm dom cod fn arg)
  apply exact_OpenChosenAuxMeasureChildCases baseM B α Γ arg goal
  intro β j Δ ma da ba keep a
  change Nonempty (Derivation B Δ ((windowAt W ctx cod (auxiliaryTerm dom cod fn arg)).relabel j))
  rw [windowRename,auxiliaryRename]
  have h := moveInputs s W T TV ctx dom cod fn arg j keep held
  have f' := moveChild baseM j Δ keep f
  exact withMeasurements s base T V TV baseM (ctx.relabel j) (dom.relabel j) (cod.relabel j) (fn.relabel j)
    (arg.relabel j) (mf.relabel j) (df.relabel j) (bf.relabel j) ma da ba h f' a

/-- Genuine selected parent window from the same two genuine child windows
and the three held type guard pairs. All measure and grammar reports,
the parent scratch and occurrence, and the successful context are chosen
by their exact physical programs in the same original calculus. -/
theorem exact_OpenStrictMeasuredFormation (s : Settings) (base : Program 2) (T V TV baseM : Program 1)
    (ctx dom cod fn arg : OTerm α) :
    let W := measuredStrictWindow s base T V TV baseM
    Inputs s W T TV B Γ ctx dom cod fn arg →
    Nonempty (Derivation B Γ (windowAt W ctx cod (auxiliaryTerm dom cod fn arg))) := by
  intro W held
  let goal := windowAt W ctx cod (auxiliaryTerm dom cod fn arg)
  apply exact_OpenChosenAuxMeasureChildCases baseM B α Γ fn goal
  intro β j Δ mf df bf keep f
  change Nonempty (Derivation B Δ ((windowAt W ctx cod (auxiliaryTerm dom cod fn arg)).relabel j))
  rw [windowRename,auxiliaryRename]
  have h := moveInputs s W T TV ctx dom cod fn arg j keep held
  exact withFunctionMeasure s base T V TV baseM (ctx.relabel j) (dom.relabel j) (cod.relabel j)
    (fn.relabel j) (arg.relabel j) mf df bf h f

#print axioms exact_OpenStrictMeasuredFormation
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralStrictMeasuredFormationProof
