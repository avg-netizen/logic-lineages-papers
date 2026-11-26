module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxMemoTransportProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMemoLeastLawsProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationRebuildProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectSelectorsProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxImageTransportProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z rawCons unary)
open NumberedWindowInternalSparseRawFunctionFrameTargets (auxiliaryTerm)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)
open NumberedWindowInternalSparseAddressPositiveOpenTargets (addressReport)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm)
open NumberedWindowInternalLiteralEnrichedEdgeProof (D)
open NumberedWindowInternalLiteralEnrichedEdgeReversalProof (CanReverse)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteScalar)
open NumberedWindowInternalLiteralRoundObserverTargets (Preserves)
open NumberedWindowInternalLiteralPackedLeastOnProof (packedLeastOn leastOnGraph)
open NumberedWindowInternalLiteralLeastOnFixedPointProof (WindowEndpoints exact_OpenLeastOnWindow)
open NumberedWindowInternalLiteralBiAuxMemoTransportProof (exact_OpenBiAuxMemoTransport)
open NumberedWindowInternalLiteralMemoRoundApplicationMotiveProof (varyAuxiliary)
open NumberedWindowInternalLiteralMemoVaryingParentProof (varyingOperandType)
open NumberedWindowInternalLiteralStrictMeasuredScratchProof (measuredStrictCover)
open NumberedWindowInternalLiteralStrictMeasuredPlainLiftProof
open NumberedWindowInternalLiteralBiAuxBaseWindowLiftProof (biAuxBaseOn)
open NumberedWindowInternalLiteralBiAuxWindowLiftProof (AuxWindowAssembly)
open NumberedWindowInternalLiteralNormalizedAuxSyntaxProof (unitAuxSyntax)
open NumberedWindowInternalLiteralTypedMemoUnfoldingProof (recursiveTypedMemo)
open NumberedWindowInternalLiteralTypedMemoLeastLawsProof (memoFilteredLeast MemoSelectedReports)
open NumberedWindowInternalLiteralApplicationRebuildProof (exact_OpenLiteralApplicationFromReportedLeast)

attribute [local irreducible] programGraph recursiveTypedMemo packedLeastOn
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- Retain the parent's actual minimum while moving both children to
their selected canonical representatives. In the argument position
only exchange of representatives is used, never an argument reduction. -/
theorem exact_OpenBiAuxCanonicalImage (s : Settings) (X : Program 2) (T V TV baseM : Program 1)
    (W : Program 3) (assembly : AuxWindowAssembly s T TV (unitAuxSyntax V TV) W)
    (ctx dom cod f a f₀ a₀ m : OTerm α) :
    let C := measuredStrictCover V TV baseM
    let Base := biAuxBaseOn s X V TV baseM W
    let E := recursiveTypedMemo Base
    CanReverse Base → WindowEndpoints W E → Preserves E (packedLeastOn C E s) →
    ParentTypeEvidence s T TV B Γ dom cod →
    D B Γ (windowAt W ctx (rawCons dom cod) f) →
    D B Γ (windowAt W ctx dom a) →
    D B Γ (leastOnGraph C E s ctx (rawCons dom cod) f f₀) →
    D B Γ (leastOnGraph C E s ctx dom a a₀) →
    D B Γ (leastOnGraph C E s ctx cod (auxiliaryTerm dom cod f a) m) →
    D B Γ (leastOnGraph C E s ctx cod (auxiliaryTerm dom cod f₀ a₀) m) := by
  intro C Base E reverse ends stable types fWindow aWindow fMin aMin parent
  have arrow (d c : OTerm α) : varyingOperandType false d c = rawCons d c := rfl
  have input (d c : OTerm α) : varyingOperandType true d c = d := rfl
  have formF (d c q a : OTerm α) : varyAuxiliary false d c q a = auxiliaryTerm d c q a := rfl
  have formA (d c q f : OTerm α) : varyAuxiliary true d c q f = auxiliaryTerm d c f q := rfl
  have af : D B Γ (windowAt W ctx (varyingOperandType true dom cod) a) := by
    rw [input]
    exact aWindow
  have ff : D B Γ (leastOnGraph C E s ctx (varyingOperandType false dom cod) f f₀) := by
    rw [arrow]
    exact fMin
  have pp : D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary false dom cod f a) m) := by
    rw [formF]
    exact parent
  have lifted := exact_OpenBiAuxMemoTransport s X T V TV baseM W assembly false
    ctx dom cod f f₀ a m reverse stable types af ff pp
  rw [formF] at lifted
  have atCanonical := exact_OpenLeastOnWindow C E s W ends ctx (rawCons dom cod) f f₀ fMin fWindow
  have fw : D B Γ (windowAt W ctx (varyingOperandType false dom cod) f₀) := by
    rw [arrow]
    exact atCanonical
  have aa : D B Γ (leastOnGraph C E s ctx (varyingOperandType true dom cod) a a₀) := by
    rw [input]
    exact aMin
  have held : D B Γ (leastOnGraph C E s ctx cod (varyAuxiliary true dom cod a f₀) m) := by
    rw [formA]
    exact lifted
  have finish := exact_OpenBiAuxMemoTransport s X T V TV baseM W assembly true
    ctx dom cod a a₀ f₀ m reverse stable types fw aa held
  rw [formA] at finish
  exact finish

#print axioms exact_OpenBiAuxCanonicalImage
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralBiAuxImageTransportProof
