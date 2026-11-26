module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedWrappedAuxTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFormationTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (allOne)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary rawCons)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSettingsGrammarGuardDefinitions (refitGuard)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)

/-- Literal original one-function formation formula; thin source recut
does not assert a native equality to the broader historical module. -/
def thinFormation {α : Type} (W : Program 3) (ctx dom cod arg : OTerm α) : Formula α :=
  let j : α → α ⊕ Fin 1 := Sum.inl
  let f : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  allOne ((windowAt W (ctx.relabel j) ((rawCons dom cod).relabel j) f).imp
    (windowAt W (ctx.relabel j) (cod.relabel j) (auxiliaryTerm (dom.relabel j) (cod.relabel j) f (arg.relabel j))))

def ExactOpenCoverCombinedRestrictedFormation : Prop :=
  ∀ (V TV M M0 : Program 1) (B : Program 2) (T : Program 1) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx dom cod arg : OTerm α),
    let P := combinedPrograms s V TV M M0 B T
    let W := thinMatchingWindow P.cover s P.W P.V
    Nonempty (Derivation body Γ (unary TV (suc z) dom ⊓ unary TV (suc z) cod)) →
    Nonempty (Derivation body Γ (unary (refitGuard s T) (suc z) dom ⊓ unary (refitGuard s T) (suc z) cod)) →
    Nonempty (Derivation body Γ (windowAt W ctx dom arg)) →
    Nonempty (Derivation body Γ (thinFormation W ctx dom cod arg))

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedFormationTargets
