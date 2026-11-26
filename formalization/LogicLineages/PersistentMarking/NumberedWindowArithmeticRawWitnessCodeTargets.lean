import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCode

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeTargets
open NumberedWindowRawWitnessBits
open NumberedWindowArithmeticWitnessListCode NumberedWindowArithmeticRawRootCode
open NumberedWindowArithmeticRawWitnessCode
universe u

def LiteralWitnessCodec {α : Type u} (enc : α → Nat) (dec : Nat → Option α) : Prop :=
  (∀ n w, dec n = some w ↔ enc w = n) ∧
  (∀ w, dec (enc w) = some w) ∧
  (∀ n, dec n = none ↔ ¬ ∃ w, enc w = n)

def ExactTermOccurrenceListCodec : Prop := LiteralWitnessCodec encodeTermList decodeTermList

def ExactReplacementWitnessCodec : Prop := LiteralWitnessCodec encodeReplacement decodeReplacement

def ExactSelectFlagCodec : Prop := LiteralWitnessCodec encodeFlag decodeFlag

def ExactRawRootWitnessCodec : Prop := LiteralWitnessCodec encodeRoot decodeRoot

def RawWitnessFuelCalibration : Prop :=
  (∀ fuel code w, decodeWitnessFuel fuel code = some w → encodeWitness w = code) ∧
  (∀ fuel w, encodeWitness w ≤ fuel → decodeWitnessFuel fuel (encodeWitness w) = some w)

def ExactRawWitnessCodec : Prop := LiteralWitnessCodec encodeWitness decodeWitness

end LogicLineages.PersistentMarking.NumberedWindowArithmeticRawWitnessCodeTargets
