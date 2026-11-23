module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticTermCode

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeTargets
open NumberedWindowSyntax
open NumberedWindowArithmeticFields NumberedWindowArithmeticTermCode

def FieldsFuelCalibration : Prop :=
  (∀ fuel code xs, decodeFieldsFuel fuel code = some xs → encodeFields xs = code) ∧
  (∀ fuel xs, encodeFields xs ≤ fuel →
    decodeFieldsFuel fuel (encodeFields xs) = some xs)

def ExactFieldsCodec : Prop :=
  (∀ code xs, decodeFields code = some xs ↔ encodeFields xs = code) ∧
  (∀ xs, decodeFields (encodeFields xs) = some xs) ∧
  (∀ code, decodeFields code = none ↔ ¬ ∃ xs, encodeFields xs = code)

def LiteralFieldBounds : Prop :=
  (∀ xs x, x ∈ xs → x < encodeFields xs) ∧
  (∀ tag xs x, x ∈ xs → x < encodeNode tag xs) ∧
  (∀ tag xs, 0 < encodeNode tag xs)

def ExactTaggedNodeCodec : Prop :=
  (∀ code tag xs, decodeNode code = some (tag,xs) ↔ encodeNode tag xs = code) ∧
  (∀ tag xs, decodeNode (encodeNode tag xs) = some (tag,xs)) ∧
  (∀ code, decodeNode code = none ↔ ¬ ∃ tag xs, encodeNode tag xs = code)

def TermFuelCalibration : Prop :=
  (∀ fuel code Q, decodeTermFuel fuel code = some Q → encodeTerm Q = code) ∧
  (∀ fuel Q, encodeTerm Q ≤ fuel →
    decodeTermFuel fuel (encodeTerm Q) = some Q)

def ArgsFuelCalibration : Prop :=
  (∀ fuel code qs, decodeArgsFuel fuel code = some qs → encodeArgs qs = code) ∧
  (∀ fuel qs, encodeArgs qs ≤ fuel →
    decodeArgsFuel fuel (encodeArgs qs) = some qs)

def ExactTermCodec : Prop :=
  (∀ code Q, decodeTerm code = some Q ↔ encodeTerm Q = code) ∧
  (∀ Q, decodeTerm (encodeTerm Q) = some Q) ∧
  (∀ code, decodeTerm code = none ↔ ¬ ∃ Q, encodeTerm Q = code)

def ExactArgsCodec : Prop :=
  (∀ code qs, decodeArgs code = some qs ↔ encodeArgs qs = code) ∧
  (∀ qs, decodeArgs (encodeArgs qs) = some qs) ∧
  (∀ code, decodeArgs code = none ↔ ¬ ∃ qs, encodeArgs qs = code)

end LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeTargets
