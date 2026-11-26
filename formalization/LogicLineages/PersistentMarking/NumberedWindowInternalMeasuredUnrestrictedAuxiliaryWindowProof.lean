module

public import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedWindowIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAuxSyntaxOpenIntroProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowThinOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxiliaryWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparseCoverScratch (scratchVertices)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc unary rawCons)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparsePackedLeast (contextOption)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparseApplicationOutputCoreReportSyntaxProof (auxiliaryRename)
open NumberedWindowInternalMeasuredUnrestrictedWindowDefinitions (window syntaxWindow contextPresent)
open NumberedWindowInternalMeasuredUnrestrictedWindowReportsProof
  (exact_OpenUnrestrictedSyntaxWindowIntro exact_OpenUnrestrictedWindowReports exact_OpenUnrestrictedContextPresentCases)
open NumberedWindowInternalMeasuredUnrestrictedWindowIntroProof
  (exact_OpenUnrestrictedContextOptionMove exact_OpenMeasuredUnrestrictedCoveredWindowIntro)
open NumberedWindowInternalAuxWindowStepTargets (intrinsicQuery windowUpdate)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowThinOpenChecks (exact_OpenAuxWindow)
open NumberedWindowInternalCoverAuxSyntaxTargets (auxSyntax auxSyntaxChildren)
open NumberedWindowInternalCoverAuxSyntaxOpenIntroProof (exact_OpenCoverAuxSyntaxIntro)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- At the actual restricted-to-own-scratch constructor, only scratch and
membership remain additional. The context witness is taken from the held
positive context guard, not presumed or chosen on a different context. -/
theorem exact_OpenUnrestrictedWindowFromSyntaxContext
    (C : Program 3) (s : Settings) (baseW : Program 3) (V : Program 1)
    (ctx childTy child parentTy parent vertices : OTerm α)
    (context : Nonempty (Derivation B Γ (windowAt contextPresent ctx childTy child)))
    (ready : Nonempty (Derivation B Γ (windowAt (syntaxWindow baseW V) ctx parentTy parent)))
    (scratch : Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices parent)))
    (own : Nonempty (Derivation B Γ (memberGraph vertices parent))) :
    Nonempty (Derivation B Γ (windowAt (window C s baseW V) ctx parentTy parent)) := by
  apply exact_OpenUnrestrictedContextPresentCases ctx childTy child _ context
  intro β j Δ payload keep parsed
  rw [windowRename]
  have atParent := exact_OpenUnrestrictedContextOptionMove (ctx.relabel j) (childTy.relabel j) (child.relabel j)
    (parentTy.relabel j) (parent.relabel j) (suc payload) parsed
  have ready' := renameInto ready j Δ keep
  have scratch' := renameInto scratch j Δ keep
  have own' := renameInto own j Δ keep
  rw [windowRename] at ready'
  rw [unaryRename] at scratch'
  rw [graphRename] at own'
  exact exact_OpenMeasuredUnrestrictedCoveredWindowIntro C s (syntaxWindow baseW V)
    (ctx.relabel j) (parentTy.relabel j) (parent.relabel j) payload (vertices.relabel j)
    ready' atParent scratch' own'

/-- The same physical selected syntax and intrinsic base query at both
children determine the actual parent window when the original parent scratch
trace and its own membership are held. The two pairs of type bits are
independent and are not identified by their numeric calibrations. -/
theorem exact_OpenMeasuredUnrestrictedAuxiliaryWindow
    (C : Program 3) (s : Settings) (base : Program 2) (T V TV : Program 1)
    (ctx dom cod fn arg vertices : OTerm α) :
    let baseW := intrinsicQuery (selectedIntrinsic (windowUpdate base T))
    let V' := auxSyntax V TV
    let W := window C s baseW V'
    let q := auxiliaryTerm dom cod fn arg
    Nonempty (Derivation B Γ (windowAt W ctx (rawCons dom cod) fn)) →
    Nonempty (Derivation B Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation B Γ (unary T (suc z) dom ⊓ unary T (suc z) cod)) →
    Nonempty (Derivation B Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation B Γ (unary (scratchVertices C s) vertices q)) →
    Nonempty (Derivation B Γ (memberGraph vertices q)) →
    Nonempty (Derivation B Γ (windowAt W ctx cod q)) := by
  intro baseW V' W q fnHeld argHeld Tguard TVguard scratch hit
  obtain ⟨f⟩ := exact_OpenUnrestrictedWindowReports C s baseW V' ctx (rawCons dom cod) fn fnHeld
  obtain ⟨a⟩ := exact_OpenUnrestrictedWindowReports C s baseW V' ctx dom arg argHeld
  obtain ⟨t⟩ := Tguard
  obtain ⟨tv⟩ := TVguard
  obtain ⟨rule⟩ := exact_OpenAuxWindow base T B α Γ ctx dom cod fn arg
  have baseAtParent : Nonempty (Derivation B Γ (windowAt baseW ctx cod q)) :=
    ⟨Derivation.implicationElimination rule (Derivation.conjunctionIntroduction t
      (Derivation.conjunctionIntroduction (Derivation.conjunctionLeft f) (Derivation.conjunctionLeft a)))⟩
  have children : Nonempty (Derivation B Γ (auxSyntaxChildren V TV dom cod fn arg)) :=
    ⟨Derivation.conjunctionIntroduction tv (Derivation.conjunctionIntroduction
      (Derivation.conjunctionLeft (Derivation.conjunctionRight f))
      (Derivation.conjunctionLeft (Derivation.conjunctionRight a)))⟩
  have syntaxAtParent : Nonempty (Derivation B Γ (unary V' (suc z) q)) :=
    exact_OpenCoverAuxSyntaxIntro V TV B α Γ dom cod fn arg children
  have ready := exact_OpenUnrestrictedSyntaxWindowIntro baseW V' ctx cod q baseAtParent syntaxAtParent
  exact exact_OpenUnrestrictedWindowFromSyntaxContext C s baseW V' ctx (rawCons dom cod) fn cod q vertices
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight f)⟩ ready scratch hit

#print axioms exact_OpenUnrestrictedWindowFromSyntaxContext
#print axioms exact_OpenMeasuredUnrestrictedAuxiliaryWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalMeasuredUnrestrictedAuxiliaryWindowProof
