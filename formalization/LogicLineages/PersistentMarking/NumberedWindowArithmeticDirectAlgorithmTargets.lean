import LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectCode
import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectAlgorithmTargets
open NumberedWindowArithmeticDirectMultisetBits NumberedWindowArithmeticAllContextBits
open NumberedWindowArithmeticDirectCode
open NumberedWindowDirectAlgorithm

def entry (e : InsertedOccurrence) : Entry := (e.target,e.dominator,e.certificate)
def witness (w : DirectMultisetWitness) : Witness := (w.kept,w.removed,w.inserted.map entry)

def LiteralOccurrenceDecoders : Prop :=
  (∀ n, readEntry n = (decodeInsertion n).map entry) ∧
  (∀ n, readWitness n = (decodeDirectWitness n).map witness)

def OriginalMultisetCheckerValues : Prop :=
  (∀ S K, typedList (addressBit S K) = typedAddressListCodeBit S K) ∧
  (∀ S K, direct (addressBit S K) (addressRSBit S K) = directMultisetCodeBit S K)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticDirectAlgorithmTargets
