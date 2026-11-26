import LogicLineages.PersistentMarking.NumberedWindowAddressApplication
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowExternalApplication
import LogicLineages.PersistentMarking.NumberedWindowPathWitnessTargets

namespace LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets
open NumberedWindowSyntax NumberedWindowSimulationData NumberedWindowExternalApplication
open NumberedWindowAddressApplication NumberedWindowArithmeticScalarTargets
open NumberedWindowArithmeticClassAddress NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticLeastClass NumberedWindowPathWitnessTargets

def decodedApplication (S : Spine.Signature) (K : List Ty) (source argument : Nat) : Option Nat := do
  let q ← decodeAddress source
  let u ← decodeAddress argument
  let .arrow domain result := q.result | none
  if canonicalBit S K q && canonicalBit S K u &&
      decide (q.context = u.context) && decide (domain = u.result) then
    let Q ← decodeTerm q.least
    let U ← decodeTerm u.least
    (leastCode S K q.context result (.auxApp domain result Q U)).map
      (fun k => encodeAddress ⟨q.context,result,k⟩)
  else none

def ExactDecodedApplication : Prop :=
  ∀ S K source argument,
    application (fixed S K) source argument = decodedApplication S K source argument

def ExactClassApplication : Prop :=
  ∀ S K Γ σ τ (hk : DecisionSourceUniverse.Closed K)
    (q : Class S K (finiteC Γ) (.arrow σ τ)) (u : Class S K (finiteC Γ) σ) i j,
    ActualCodeAt S K Γ (.arrow σ τ) i q → ActualCodeAt S K Γ σ j u →
      ∀ value, decodedApplication S K (encodeAddress ⟨Γ,.arrow σ τ,i⟩)
        (encodeAddress ⟨Γ,σ,j⟩) = some value ↔
        ∃ k, value = encodeAddress ⟨Γ,τ,k⟩ ∧
          ActualCodeAt S K Γ τ k (appClass hk q u)

end LogicLineages.PersistentMarking.NumberedWindowAddressApplicationTargets
