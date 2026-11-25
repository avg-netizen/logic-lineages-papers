module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedCanonicalCarrierProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralNeutralResidualProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCanonicalSourceCarrierProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedCanonicalEndpointProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAccessibilityRules (carrier)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalLiteralCoveredMemo (coveredMemoWindow WindowSeedsCovered)
open NumberedWindowInternalLiteralCoveredTypedAuxCasesProof (ActiveRaw)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalMeasuredPairedGuardedThinNumericProof (pairedExchange)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralRoundLeastTargets (SameLeastOnEdge)
open NumberedWindowInternalSparsePackedLeast (packedLeastProgram)
open NumberedWindowInternalSparseApplicationFrontend (applicationCore)
open NumberedWindowInternalSparseApplicationReinstall (frontendInputs)
open NumberedWindowInternalSparseCanonicalAddressThinDefinitions (addressScalar)
open NumberedWindowInternalLiteralPairedCanonicalCarrierProof (exact_ConcretePairedCanonicalCarrierPacket)
open NumberedWindowInternalLiteralDirectCarrierInstalledProof (Packet)
open NumberedWindowInternalLiteralNeutralResidualProof (Body Step)
open NumberedWindowInternalNeutralFactsTargets (D direct)
open NumberedWindowInternalLiteralRootDispatchNumericProof (root)
open NumberedWindowInternalLiteralAuxRootLeaf (leafAtAuxiliary)
open NumberedWindowInternalLiteralAuxFallback (auxiliaryFallback)
open NumberedWindowInternalLiteralBoundedFallback (fallback)

/-- Both endpoint carriers are derived for the ordinary direct graph
of the same scalar/body packet, not inferred from an unrelated guard. -/
def EndpointCarriers (i cv tv : Program 1) (R : Program 5) (L : Program 3) : Prop :=
  ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (x y : OTerm α),
    let S := Body i cv tv R L
    D S c Γ (direct S (Step i cv tv R L) c x y) →
      D S c Γ (carrier S false c x ⊓ carrier S false c y)

theorem exact_OriginalPairedCanonicalEndpointPacket (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) (seeds : WindowSeedsCovered s)
    (symmetric : HeadPairsSymmetric s.equivalentHeads) :
    ∃ (cv tv : Program 1) (leaf : Nat → Program 3) (C other : Program 3) (d base : Program 2)
      (T V : Program 1) (v : Inputs),
      let X := guardedExchange C s (pairedExchange d)
      let win := coveredMemoWindow C s base T V
      let R := ActiveRaw C s leaf other base T V
      let L := packedLeastProgram C X win s
      let i := addressScalar cv tv win L
      Packet xs s W i cv tv R L (applicationCore L) (frontendInputs i L v) ∧
      SameLeastOnEdge C X win s ∧ EndpointCarriers i cv tv R L := by
  obtain ⟨_,cv,tv,leaf,C,other,d,base,T,V,v,_,packet,coherent⟩ :=
    exact_ConcretePairedCanonicalCarrierPacket xs s W valid seeds symmetric
  refine ⟨cv,tv,leaf,C,other,d,base,T,V,v,packet,coherent,?_⟩
  intro c α Γ x y data edge
  exact NumberedWindowInternalLiteralCanonicalSourceCarrierProof.exact_OpenCanonicalDirectCarriers
    cv tv C (root (leafAtAuxiliary leaf)) (auxiliaryFallback (fallback other))
    (coveredMemoWindow C s base T V) (guardedExchange C s (pairedExchange d)) V s coherent c x y edge

#print axioms exact_OriginalPairedCanonicalEndpointPacket
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralPairedCanonicalEndpointProof
