module
public import LogicLineages.PersistentMarking.NumberedWindowInternalOwnCoverReportsTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseIntrinsicInstallationTargets
@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoveredFormationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons suc z)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalAuxWindowStepTargets (windowUpdate intrinsicQuery)
open NumberedWindowInternalOwnCoverReportsTargets (syntaxFlag)
open NumberedWindowInternalFactoredCoverTargets (factoredCover)
open NumberedWindowInternalSparseStructuralApplicationTargets (window)
open NumberedWindowInternalSparseCoverOccurrenceTargets (occursInCover)

def ExactCoveredFormation : Prop := ∀ (baseV M : Program 1) (G : Program 3) (s : Settings)
    (intrinsicBase : Program 2) (T : Program 1) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (ctx dom cod f arg : OTerm α),
  let V := syntaxFlag baseV
  let C := factoredCover V M G
  let K := intrinsicQuery (selectedIntrinsic (windowUpdate intrinsicBase T))
  let W := window C s K V
  let parent := auxiliaryTerm dom cod f arg
  let types := unary T (suc z) dom ⊓ unary T (suc z) cod
  let children := windowAt W ctx (rawCons dom cod) f ⊓ windowAt W ctx dom arg
  Nonempty (Derivation body Γ (((types ⊓ children) ⊓ occursInCover C s parent parent).imp
    (windowAt W ctx cod parent)))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoveredFormationTargets
