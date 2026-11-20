import LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets

namespace LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppTargets
open NumberedWindowAddressApplication (application graph)
open NumberedWindowAddressApplicationTargets (decodedApplication)
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticClassAddress (encodeAddress)
open NumberedWindowArithmeticAllContextBits (canonicalBit)
open NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticLeastClass (finiteC)
open NumberedWindowExternalApplication (appClass)

/-- The exact optional application on the actual two literal canonical
 addresses, with the original context and arrow domain in their own fields.
 This narrower lemma does not assert the whole malformed-input decoder law. -/
def ExactCanonicalLiteralApplication : Prop :=
  ∀ (S : Spine.Signature) (K Γ : List Ty) (σ τ : Ty) (i j : Nat),
    canonicalBit S K ⟨Γ,.arrow σ τ,i⟩ = true →
    canonicalBit S K ⟨Γ,σ,j⟩ = true →
    application (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) (encodeAddress ⟨Γ,σ,j⟩) =
      decodedApplication S K (encodeAddress ⟨Γ,.arrow σ τ,i⟩) (encodeAddress ⟨Γ,σ,j⟩)

/-- Keep the original raw graph, same argument code, same original
 quotient class and actual result code. No new application operation. -/
def ExactCanonicalLiteralApplicationGraph : Prop :=
  ∀ (S : Spine.Signature) (K Γ : List Ty) (σ τ : Ty) (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K (finiteC Γ) (.arrow σ τ)) (u : Class S K (finiteC Γ) σ) (i j : Nat),
    ActualCodeAt S K Γ (.arrow σ τ) i q → ActualCodeAt S K Γ σ j u →
    ∀ v, graph (fixed S K) (encodeAddress ⟨Γ,.arrow σ τ,i⟩) (encodeAddress ⟨Γ,σ,j⟩) v = true ↔
      ∃ k, v = encodeAddress ⟨Γ,τ,k⟩ ∧ ActualCodeAt S K Γ τ k (appClass hk q u)

end LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchCanonicalAppTargets
