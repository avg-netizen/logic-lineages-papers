import LogicLineages.PersistentMarking.NumberedWindowShiftAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCode

namespace LogicLineages.PersistentMarking.NumberedWindowShiftTargets
open NumberedWindowShiftAlgorithm NumberedWindowArithmeticTermCode NumberedWindowSyntax

def ExactShiftMatrix : Prop :=
  (∀ amount cutoff bound offset Q, encodeTerm Q + offset ≤ bound →
    (computed amount cutoff bound (encodeTerm Q) offset).1 =
      encodeTerm (shift amount (cutoff+offset) Q)) ∧
  (∀ amount cutoff bound offset qs, encodeArgs qs + offset ≤ bound →
    (computed amount cutoff bound (encodeArgs qs) offset).2 =
      encodeArgs (shiftArgs amount (cutoff+offset) qs))

def ExactShiftOutput : Prop :=
  ∀ amount cutoff n, output amount cutoff n =
    ((decodeTerm n).map (fun q => encodeTerm (shift amount cutoff q)),
      (decodeArgs n).map (fun qs => encodeArgs (shiftArgs amount cutoff qs)))

end LogicLineages.PersistentMarking.NumberedWindowShiftTargets
