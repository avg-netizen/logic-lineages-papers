module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoAuxRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoAuxRowProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoAuxParentProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqnRelabel sucRelabel zRelabel)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (rawConsRename unaryRename)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalChosenAuxMeasureMemoTargets (memoPrior)
open NumberedWindowInternalChosenAuxMeasureObservedSyntaxProof (priorRename)
open NumberedWindowInternalAuxWindowOpenTargets (windowGraph)
open NumberedWindowInternalLiteralSyntaxMemoWindow
open NumberedWindowInternalLiteralSyntaxMemoWindowRowProof (D exact_OpenContextWindowRow)
open NumberedWindowInternalLiteralSyntaxMemoWindowSoundProof (windowRename)
open NumberedWindowInternalLiteralSyntaxMemoAuxRowProof

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem factsRename {β : Type} (base : Program 2) (T V : Program 1)
    (ctx ty dom cod fn arg : OTerm α) (j : α → β) :
    (actualAuxChildren base T V ctx ty dom cod fn arg).relabel j =
      actualAuxChildren base T V (ctx.relabel j) (ty.relabel j) (dom.relabel j) (cod.relabel j)
        (fn.relabel j) (arg.relabel j) := by
  simp only [actualAuxChildren,childAtWindow,conjunctionRename,eqnRelabel,unaryRename,
    windowRename,sucRelabel,zRelabel,rawConsRename]

/-- For the actual successful parent in the physical syntax memo,
both children have the exact same chosen typed-window and raw-syntax
programs. The original stored result is identified with the queried
type; neither context nor numeric raw codes are inferred or replaced. -/
theorem exact_OpenSyntaxMemoAuxParent (base : Program 2) (T V : Program 1)
    (ctx ty dom cod fn arg : OTerm α)
    (held : D B Γ (windowGraph (window base T V) ctx ty (auxiliaryTerm dom cod fn arg))) :
    D B Γ (actualAuxChildren base T V ctx ty dom cod fn arg) := by
  apply exact_OpenContextWindowRow (update base T V) ctx (memoPrior dom cod fn arg) ty _ held
  intro β j Δ old _ tab row
  rw [priorRename] at tab row
  rw [factsRename]
  exact exact_OpenSyntaxMemoAuxRow base T V (ctx.relabel j) (ty.relabel j) (dom.relabel j)
    (cod.relabel j) (fn.relabel j) (arg.relabel j) old tab row

#print axioms exact_OpenSyntaxMemoAuxParent
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralSyntaxMemoAuxParentProof
