module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicRawInstalledProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteApplicationClosureProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFormingCoherenceProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepPrograms
import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedEdgeCoherenceProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralAtomicLeastShapeProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHeaderLeastGuardProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseLeastInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationReinstallChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScalarReinstallThinProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalScalarNumericProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteApplicationInstalledProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered coveredMemoWindow)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalLiteralPairedAuxInstalledProof (exact_ConcretePairedCoveredTypedAuxTuple)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralCanonicalScalarNumericProof (exact_LiteralAddressScalarCalibration)
open NumberedWindowInternalLiteralScalarReinstallThinProof (exact_ReinstallLiteralScalar)
open NumberedWindowInternalSparseLeastInstallationChecks (exact_ReinstallCalibratedLeast)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore applicationGuard)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseApplicationReinstallChecks (exact_ReinstallGuardedApplicationTuple)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalLiteralCount (permutation)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalLiteralAtomicRawGuardProof (guardedRaw)
open NumberedWindowInternalLiteralAtomicRawInstalledProof (exact_ReinstallLiteralAtomicRawPacket)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast exact_LiteralAtomicGuardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast exact_LiteralHeaderLeast)

open NumberedWindowInternalLiteralFiniteScalarGuardProof (D finiteCodes finiteScalar exact_LiteralFiniteScalarCalibration)
open NumberedWindowInternalLiteralApplicationCoverageWindowProof
  (coveredFormationWindow exact_CoveredFormationWindowCalibration exact_OpenCoveredFormationWindow)
open NumberedWindowInternalLiteralCoveredMemoLeastProof (exact_OpenLeastFromCoverage)
open NumberedWindowInternalLiteralFormingCoherenceProof (exact_OpenCoherenceFromWindowDomain)
open NumberedWindowInternalLiteralPairedEdgeCoherenceProof (exact_OriginalPairedSelectedMinimum)
open NumberedWindowInternalAuxWindowStepPrograms (exact_WindowPrimitiveLeaves)
open NumberedWindowInternalAuxWindowStepChecks (exact_PhysicalAuxWindow)
open NumberedWindowInternalSparsePackedLeastNumericChecks (exact_PackedLeastComposition)
open NumberedWindowInternalLiteralFiniteApplicationClosureProof (exact_OpenLiteralFiniteApplicationClosure)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S)
open NumberedWindowInternalLiteralNeutralAtomProof (neutralSource)
open NumberedWindowInternalNeutralFactsTargets (atom)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)

/-- Place a separately selected forming window into the least and scalar
slots. Keep the original physical raw route as a named program, and rebuild
the installed tuple without identifying it with any numerically equal AST.
The same newly installed body carries the two open application conclusions. -/
theorem exact_ConcretePairedFiniteApplicationPacket (xs : Entries) (s : Settings) (P : List ProbeTy)
    (valid : ValidWindow s P) (seeds : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads)
    (included : ∀ ty ∈ finiteCodes P, ty ∈ s.window.1) :
    ∃ (cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3)
      (directed rawBase base : Program 2) (rawT V T : Program 1) (placed : Inputs),
      let X := guardedExchange C s (pairedExchange directed)
      let W := coveredFormationWindow C s base T
      let raw := ActiveRaw C s leaf other rawBase rawT V
      let L := guardedLeast (headerLeast (packedLeastProgram C X W s))
      let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
      Packet xs s P i cv tv (guardedRaw raw) L (applicationCore L) placed ∧
      SameLeastOnEdge C X W s ∧
      (∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (f u y : OTerm α),
        let data := S i cv tv (rawWithTarget i cv tv (guardedRaw raw) L) L
        let B := sourceBody data c
        D B Γ (programGraph (applicationGuard i L) (suc z) ![f,u,y]) →
        D B Γ (carrier data false c y) ∧ D B Γ (atom neutralSource y)) := by
  obtain ⟨oldI,cv,tv,leaf,C,other,directed,rawBase,rawT,V,v,orig,_⟩ :=
    exact_ConcretePairedCoveredTypedAuxTuple xs s P valid seeds symmetric
  obtain ⟨base,T,baseFit,TFit⟩ := exact_WindowPrimitiveLeaves s
  let X := guardedExchange C s (pairedExchange directed)
  let W := coveredFormationWindow C s base T
  let raw := ActiveRaw C s leaf other rawBase rawT V
  let oldL := packedLeastProgram C X (coveredMemoWindow C s rawBase rawT V) s
  let L₀ := packedLeastProgram C X W s
  let L := guardedLeast (headerLeast L₀)
  let i := finiteScalar (addressScalar cv tv W L) (finiteCodes P)
  let r := addressPositive cv tv raw oldL
  let d := dCore oldI r permutation
  have windowFit := exact_CoveredFormationWindowCalibration C s base T orig.coverFit seeds
    (exact_PhysicalAuxWindow s base T baseFit TFit)
  have leastFit := exact_PackedLeastComposition s C X W orig.coverFit orig.exchangeFit windowFit
  have head := exact_LiteralHeaderLeast s L₀ leastFit
  have hL := exact_LiteralAtomicGuardedLeast s (headerLeast L₀) head
  have lifted := exact_ReinstallCalibratedLeast xs s P valid oldI (jRaw oldI) cv tv d (applicationCore oldL)
    raw oldL L v orig.physical hL
  let v₀ := frontendInputs oldI L v
  have app := (exact_ReinstallGuardedApplicationTuple xs s P valid oldI (jRaw oldI)
    cv tv d (applicationCore oldL) raw L v lifted).2
  have calls := orig.physical.2.2.1
  have scalarFit := exact_LiteralAddressScalarCalibration s cv tv W L calls.1 calls.2.1 windowFit hL
  have cal := exact_LiteralFiniteScalarCalibration s (addressScalar cv tv W L) P valid.1 scalarFit
  have rebuilt := (exact_ReinstallLiteralScalar xs s P valid i oldI (jRaw oldI) cv tv d
    (applicationCore L) raw L v₀ cal app).2
  have coherent : SameLeastOnEdge C X W s := by
    apply exact_OpenCoherenceFromWindowDomain C X W s (exact_OriginalPairedSelectedMinimum C directed W s)
    intro B α Γ ctx ty seed held
    exact exact_OpenLeastFromCoverage C X W s ctx ty seed
      ((exact_OpenCoveredFormationWindow C s base T ctx ty seed).1 held).2
  refine ⟨cv,tv,leaf,C,other,directed,rawBase,base,rawT,V,T,frontendInputs i L v₀,
    exact_ReinstallLiteralAtomicRawPacket xs s P valid i (jRaw oldI) cv tv d (applicationCore L)
      raw L (frontendInputs i L v₀) rebuilt,coherent,?_⟩
  intro c α Γ f u y data B accepted
  exact exact_OpenLiteralFiniteApplicationClosure s P valid.2.1 cv tv T base C X
    calls.2.1 TFit included coherent raw c f u y accepted

#print axioms exact_ConcretePairedFiniteApplicationPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralFiniteApplicationInstalledProof
