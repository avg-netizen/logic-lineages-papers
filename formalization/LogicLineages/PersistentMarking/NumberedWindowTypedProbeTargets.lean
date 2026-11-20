import LogicLineages.PersistentMarking.NumberedWindowTypedProbe
import LogicLineages.PersistentMarking.NumberedWindowFreeAddressTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationGraphTargets
namespace LogicLineages.PersistentMarking.NumberedWindowTypedProbeTargets
open NumberedWindowTypedProbe NumberedWindowFreeAddress
open NumberedWindowArithmeticScalarTargets (fixed)
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticLeastClass NumberedWindowArithmeticTyCode
open NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowAddressApplication (graph)
open NumberedWindowFreeAddressTargets (FreeAt)
def ExactTypedAddress : Prop :=
  ∀ S K (hk : DecisionSourceUniverse.Closed K) (τ : Ty) n,
    typed (fixed S K) (encodeTy τ) n = true ↔ ∃ (Γ : List Ty) (i : Nat) (q : Class S K (finiteC Γ) τ),
      n = encodeAddress ⟨Γ,τ,i⟩ ∧ ActualCodeAt S K Γ τ i q

def FreshProbeApplication : Prop :=
  ∀ S K (hk : DecisionSourceUniverse.Closed K) (σ τ : Ty) n,
    typed (fixed S K) (encodeTy (.arrow σ τ)) n = true →
      ∃ (Γ : List Ty) (i : Nat) (q : Class S K (finiteC Γ) (.arrow σ τ)) (u v : Nat),
        n = encodeAddress ⟨Γ,.arrow σ τ,i⟩ ∧ ActualCodeAt S K Γ (.arrow σ τ) i q ∧
        u = freeAddress (Γ.map encodeTy) (encodeTy σ) (freshName i) ∧
        FreeAt S K Γ hk σ (freshName i) ∧ probe (fixed S K) n = some u ∧
        graph (fixed S K) n u v = true ∧ typed (fixed S K) (encodeTy τ) v = true
end LogicLineages.PersistentMarking.NumberedWindowTypedProbeTargets
