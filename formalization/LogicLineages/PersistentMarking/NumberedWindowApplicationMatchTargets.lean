import LogicLineages.PersistentMarking.NumberedWindowApplicationMatch
import LogicLineages.PersistentMarking.NumberedWindowArithmeticScalarTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticAllContextBits

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationMatchTargets
open Spine
open NumberedWindowApplicationMatch NumberedWindowAddressApplication
open NumberedWindowArithmeticScalarTargets NumberedWindowArithmeticAllContextBits

/-- Original backward matching on arbitrary address numerals. The same
supplied certificate and fixed argument drive the positive image path. -/
def ExactBackwardAddressMatching : Prop :=
  ∀ (S : Signature) (K : List Ty), DecisionSourceUniverse.Closed K →
    ∀ source target argument value certificate,
      addressRSBit S K source certificate target = true →
      graph (fixed S K) target argument value = true →
      ∃ before output,
        matchingCertificate (fixed S K) source argument certificate = some (before,output) ∧
        graph (fixed S K) source argument before = true ∧
        addressRSBit S K before output value = true

end LogicLineages.PersistentMarking.NumberedWindowApplicationMatchTargets
