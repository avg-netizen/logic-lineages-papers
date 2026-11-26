import LogicLineages.PersistentMarking.NumberedWindowApplicationMatchTargets

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationForwardTargets
open Spine
open NumberedWindowApplicationMatch NumberedWindowAddressApplication
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticAllContextBits

/-- A supplied positive function-side path can be lifted starting from a known
application result. Both applications use the unchanged actual argument address. -/
def ExactForwardAddressMatching : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ source target argument value certificate,
      addressRSBit S K source certificate target = true →
      graph (fixed S K) source argument value = true →
      ∃ next output,
        matchingCertificate (fixed S K) source argument certificate = some (value,output) ∧
        graph (fixed S K) target argument next = true ∧
        addressRSBit S K value output next = true

end LogicLineages.PersistentMarking.NumberedWindowApplicationForwardTargets
