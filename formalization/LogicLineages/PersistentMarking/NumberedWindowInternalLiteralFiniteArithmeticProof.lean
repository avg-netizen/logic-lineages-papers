module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteApplicationInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicResidualProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteArithmeticProof

open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalNeutralFactsTargets (Arithmetic D atom direct inherited)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalAtomicRefinement (freeSource bottomSource)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (acceptsGraph)
open NumberedWindowInternalLiteralNeutralResidualProof (exact_LiteralArithmeticFromResidual)
open NumberedWindowInternalLiteralAtomicResidualProof (AtomBody AtomStep)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource exact_LiteralNeutralFromApplications)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard applicationCore)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalLiteralFiniteScalarGuardProof (finiteCodes finiteScalar)
open NumberedWindowInternalLiteralApplicationCoverageWindowProof (coveredFormationWindow)
open NumberedWindowInternalLiteralFiniteApplicationClosureProof (exact_OpenLiteralFiniteApplicationClosure)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets (ActualTypeGuard)
open NumberedWindowInternalAuxWindowStepTargets (TypeGuardCalibrated)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ChildClosed)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)

/-- Only the original neutral-application inversion clause is left in
the neutral arithmetic interface. The endpoint and application guards
remain actual named programs on the same body, not just numerical
equivalences. Positive application forward transport is separate. -/
def Inversion (s : Data) (p h : Program 3) (c : Nat) : Prop :=
  ∀ (α : Type) (Γ : List (Formula α)) (x u t y : OTerm α),
    D s c Γ (atom neutralSource x) → D s c Γ (accepts p x u t) →
    D s c Γ (direct s h c t y) →
    D s c Γ (atom bottomSource y ⊔ inherited s p h c x u y)

theorem exact_LiteralFiniteArithmeticFromInversion (xs : Entries) (s : Settings) (P : List ProbeTy)
    (closed : ChildClosed P) (cv tv T : Program 1) (base : Program 2) (C : Program 3) (X : Program 2)
    (tvFit : ActualTypeGuard tv) (TFit : TypeGuardCalibrated s T)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1)
    (paid : SameLeastOnEdge C X (coveredFormationWindow C s base T) s)
    (raw : Program 5) (placed : Inputs) (c : Nat) :
    let W := coveredFormationWindow C s base T
    let L₀ := headerLeast (packedLeastProgram C X W s)
    let L := guardedLeast L₀
    let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
    let a := AtomBody i cv tv raw L₀
    let h := AtomStep i cv tv raw L₀
    Packet xs s P i cv tv (guardedRaw raw) L (applicationCore L) placed →
    Inversion a placed.applicationGuard h c →
    Arithmetic a placed.applicationGuard h neutralSource bottomSource freeSource c := by
  intro W L₀ L i a h packet invert
  have physical : placed.applicationGuard = applicationGuard i L := packet.physical.2.1
  apply exact_LiteralArithmeticFromResidual i cv tv (guardedRaw raw) L placed.applicationGuard
    neutralSource bottomSource c packet.directRules
  apply exact_LiteralNeutralFromApplications i cv tv raw L₀ placed.applicationGuard c
  refine ⟨?_,invert⟩
  intro α Γ f u y _ accepted
  rw [physical,acceptsGraph] at accepted
  exact exact_OpenLiteralFiniteApplicationClosure s P closed cv tv T base C X
    tvFit TFit included paid raw c f u y accepted

#print axioms exact_LiteralFiniteArithmeticFromInversion
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteArithmeticProof
