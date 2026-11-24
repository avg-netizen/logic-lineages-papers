module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectTargetCarrierProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralMemoTypedAuxInstalledProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralHopCarrierNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseTypedRawInstallationChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPhysicalInstallationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalOriginalFirstHopAddressProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectCarrierInstalledProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (edge carrier)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalSparseTuple (InstalledTupleAt)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalSparseApplicationFrontendTargets (ActualScalarCalibration)
open NumberedWindowInternalOriginalFirstHopCoreProof (D)
open NumberedWindowInternalLiteralAddressedChildReportsProof (S hop)
open NumberedWindowInternalNeutralFactsTargets (direct firstHop)
open NumberedWindowInternalLiteralHopCarrier (rawWithTarget)
open NumberedWindowInternalLiteralHopCarrierNumericProof (exact_RawWithTargetCalibration)
open NumberedWindowInternalLiteralDirectTargetCarrierProof (exact_OpenDirectTargetCarrier)
open NumberedWindowInternalOriginalFirstHopAddressProof (exact_OrdinaryFirstHop)
open NumberedWindowInternalSparseTypedRawInstallationChecks (exact_ReinstallCalibratedRawTuple)
open NumberedWindowInternalLiteralPhysicalInstallationProof (exact_ReinstallPhysicalLiteralMultisets)
open NumberedWindowInternalLiteralMemoTypedAuxInstalledProof (exact_ConcreteMemoTypedAuxTuple)
open NumberedWindowInternalLiteralMemoTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalDirectTypedListTargets (jRaw)
open NumberedWindowInternalDirectCoreTargets (dCore)
open NumberedWindowInternalLiteralCount (permutation)

abbrev Raw (i cv tv : Program 1) (raw : Program 5) (L : Program 3) := rawWithTarget i cv tv raw L

/-- The two path/edge obligations of the neutral-arithmetic interface
hold for the same installed original body and same direct program. -/
structure DirectRules (i cv tv : Program 1) (raw : Program 5) (L : Program 3) : Prop where
  first : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    let R := Raw i cv tv raw L
    let data := S i cv tv R L
    let h := hop cv tv R L
    let B := sourceBody data c
    D B Γ (edge data false c x y) → D B Γ (firstHop data h c x y)
  targetCarrier : ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    let R := Raw i cv tv raw L
    let data := S i cv tv R L
    let h := hop cv tv R L
    let B := sourceBody data c
    D B Γ (direct data h c x y) → D B Γ (carrier data false c y)

structure Packet (xs : Entries) (s : Settings) (W : List ProbeTy)
    (i cv tv : Program 1) (raw : Program 5) (L p₀ : Program 3) (v : Inputs) : Prop where
  physical : let R := Raw i cv tv raw L
    let r := addressPositive cv tv R L
    InstalledTupleAt xs s W i (jRaw i) cv tv (dCore i r permutation) p₀ R L v
  directRules : DirectRules i cv tv raw L

theorem exact_ReinstallLiteralDirectCarrier (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (i j cv tv : Program 1) (d p₀ : Program 3)
    (raw : Program 5) (L : Program 3) (v : Inputs)
    (old : InstalledTupleAt xs s W i j cv tv d p₀ raw L v) :
    Packet xs s W i cv tv raw L p₀ v := by
  let R := Raw i cv tv raw L
  have iFit : ActualScalarCalibration s i := old.1.1.1
  have held := old.2.2.1
  have fit := exact_RawWithTargetCalibration xs s i cv tv raw L iFit held.1 held.2.1
    held.2.2.1 held.2.2.2.1
  have newly := exact_ReinstallCalibratedRawTuple xs s W valid i j cv tv d p₀ raw R L v old fit
  have installed := (exact_ReinstallPhysicalLiteralMultisets xs s W valid i j cv tv d p₀ R L v newly).1
  exact ⟨installed,⟨fun c α Γ x y => exact_OrdinaryFirstHop i cv tv R L c α Γ x y,
    fun c α Γ x y => exact_OpenDirectTargetCarrier i cv tv raw L c x y⟩⟩

/-- Real physical instance from the same original window. The guard
works at every raw input; no extra cover hypothesis or scalar
accessibility conclusion is introduced. -/
theorem exact_ConcreteLiteralDirectCarrierTuple (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) :
    ∃ (i cv tv : Program 1) (raw : Program 5) (L p₀ : Program 3) (v : Inputs),
      Packet xs s W i cv tv raw L p₀ v := by
  obtain ⟨i,cv,tv,leaf,other,base,T,V,L,p₀,v,old⟩ := exact_ConcreteMemoTypedAuxTuple xs s W valid
  let raw := ActiveRaw leaf other base T V
  exact ⟨i,cv,tv,raw,L,p₀,v,
    exact_ReinstallLiteralDirectCarrier xs s W valid i (jRaw i) cv tv
      (dCore i (addressPositive cv tv raw L) permutation) p₀ raw L v old.physical⟩

#print axioms exact_ReinstallLiteralDirectCarrier
#print axioms exact_ConcreteLiteralDirectCarrierTuple
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralDirectCarrierInstalledProof
