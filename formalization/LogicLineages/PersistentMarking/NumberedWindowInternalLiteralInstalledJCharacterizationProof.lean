module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralJCharacterizationProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralEndpointInstallationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInstalledJCharacterizationProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus
open ID1Completion.InternalAccessibilityRules (carrier membership)
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.SourcePresentation (sourceBody)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeDispatchWindowTargets (ProbeTy ValidWindow)
open NumberedWindowInternalFreshProbeParsedTyped (Inputs)
open NumberedWindowInternalSparseAddressPositive (addressPositive)
open NumberedWindowInternalDirectTypedUnionLiteralJTargets (literalData)
open NumberedWindowInternalLiteralRawMembersJProof (allRawMembers)
open NumberedWindowInternalLiteralPermutedDirectSpliceProof (D)
open NumberedWindowInternalLiteralEndpointInstallationProof
  (LiteralEndpointPacket selectedR exact_ConcreteLiteralEndpointPacket)
open NumberedWindowInternalLiteralJCharacterizationProof (exact_EndpointLiteralJCharacterization)

/-- The J characterization belongs to the actual selected four-calibrated
programs in the original window, with the same application and probe
packet. The remaining scalar I proof is not assumed or hidden. -/
theorem exact_ConcreteLiteralJCharacterization (xs : Entries) (s : Settings) (W : List ProbeTy)
    (valid : ValidWindow s W) :
    ∃ (i cv tv : Program 1) (raw : Program 5) (least p₀ : Program 3) (v : Inputs),
      LiteralEndpointPacket xs s W i cv tv raw least p₀ v ∧
        ∀ (c : Nat) (α : Type) (Γ : List (Formula α)) (m : OTerm α),
          let S := literalData i (selectedR i cv tv raw least)
          let B := sourceBody S c
          D B Γ (membership true m) ↔
            D B Γ (carrier S true c m) ∧ D B Γ (allRawMembers m) := by
  obtain ⟨i,cv,tv,raw,least,p₀,v,packet⟩ := exact_ConcreteLiteralEndpointPacket xs s W valid
  exact ⟨i,cv,tv,raw,least,p₀,v,packet,fun c α Γ m =>
    exact_EndpointLiteralJCharacterization i (addressPositive cv tv raw least) c α Γ m⟩

#print axioms exact_ConcreteLiteralJCharacterization
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralInstalledJCharacterizationProof
