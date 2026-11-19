import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCode
import LogicLineages.PersistentMarking.NumberedWindowRawWitnessBits

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCode
open NumberedWindowArithmeticFields NumberedWindowArithmeticRawRootCode NumberedWindowRawWitnessBits

/-- Literal finite witnesses, retaining every ordered context index.
The actual encoded recursive child is a strict field below its parent. -/
def encodeWitness : RawWitness → Nat
  | .root w => encodeNode 0 [encodeRoot w]
  | .lam w => encodeNode 1 [encodeWitness w]
  | .ordinaryBase i w => encodeNode 2 [i,encodeWitness w]
  | .numberedBase i w => encodeNode 3 [i,encodeWitness w]
  | .numberedExtra i w => encodeNode 4 [i,encodeWitness w]
  | .auxFunction w => encodeNode 5 [encodeWitness w]

def assembleWitness (child : Nat → Option RawWitness) : Nat → List Nat → Option RawWitness
  | 0, [w] => (decodeRoot w).map RawWitness.root
  | 1, [w] => (child w).map RawWitness.lam
  | 2, [i,w] => (child w).map (RawWitness.ordinaryBase i)
  | 3, [i,w] => (child w).map (RawWitness.numberedBase i)
  | 4, [i,w] => (child w).map (RawWitness.numberedExtra i)
  | 5, [w] => (child w).map RawWitness.auxFunction
  | _, _ => none

def decodeWitnessFuel : Nat → Nat → Option RawWitness
  | 0, _ => none
  | f+1, n => (decodeNode n).bind (fun p => assembleWitness (decodeWitnessFuel f) p.1 p.2)

def decodeWitness (n : Nat) : Option RawWitness := decodeWitnessFuel n n

end LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCode
