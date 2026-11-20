import LogicLineages.PersistentMarking.NumberedWindowFreeAddress
import LogicLineages.PersistentMarking.NumberedWindowExternalTypeFactsTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextBits
import LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverSyntax

namespace LogicLineages.PersistentMarking.NumberedWindowFreeAddressTargets
open Spine NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowPathWitnessTargets
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTyCode NumberedWindowArithmeticLeastClass
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextBits
open NumberedWindowFreeAddress NumberedWindowExternalComputability NumberedWindowPrimaryCoverSyntax

def FreeAt (S : Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (σ : Ty) (name : Nat) : Prop :=
  ∃ U : WindowCarrier S K (finiteC Γ) σ,
    U.val = .free σ name ∧
    freeAddress (Γ.map encodeTy) (encodeTy σ) name = encodeAddress ⟨Γ,σ,encodeTerm U.val⟩ ∧
    ActualCodeAt S K Γ σ (encodeTerm U.val) (classOf U) ∧
    addressBit S K (freeAddress (Γ.map encodeTy) (encodeTy σ) name) = true ∧
    ComputableClass S K Γ hk σ (classOf U)

def ExactFreeAddress : Prop :=
  ∀ (S : Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (σ : Ty), σ ∈ K → ∀ name, FreeAt S K Γ hk σ name

/-- The arrow domain is present in the actual window and the selected
name is strictly beyond the numeral bound of the literal canonical term. -/
def ExactFreshArrowProbe : Prop :=
  ∀ (S : Signature) (K Γ : List Ty) (hk : DecisionSourceUniverse.Closed K)
    (σ τ : Ty) (q : Class S K (finiteC Γ) (.arrow σ τ)) i,
    ActualCodeAt S K Γ (.arrow σ τ) i q →
      ∃ Q : WindowCarrier S K (finiteC Γ) (.arrow σ τ),
        decodeTerm i = some Q.val ∧ classOf Q = q ∧
        freshName i = (termBounds Q.val).numeral + 1 ∧
        FreeAt S K Γ hk σ (freshName i)

end LogicLineages.PersistentMarking.NumberedWindowFreeAddressTargets
