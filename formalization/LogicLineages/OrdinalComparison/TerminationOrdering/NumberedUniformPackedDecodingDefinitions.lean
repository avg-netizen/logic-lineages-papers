module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecoding
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedNumericDecoding
open NumberedNumericCarrier

abbrev RawPacked (n : Nat) := Ty × Code (Fin n)

/-- Retain the original structural pair exactly when its actual typed decoder succeeds. -/
def rawStructuralDecode {n : Nat} (arity : Fin n → Nat) (Gamma : List Ty)
    (raw : RawPacked n) : Option (RawPacked n) :=
  bif (decodeTerm arity Gamma raw.1 raw.2).isSome then some raw else none

/-- Recover the original raw type/code pair after the unchanged numeric validity check.
The success Boolean already has a proved computation joint in the context. -/
def rawPackedDecode (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) : Option (RawPacked n) :=
  bif (decodePackedNumber n arity Gamma value).isSome then do
    let tau ← decodeType (Nat.unpair value).1
    let code ← decodeCode n (Nat.unpair value).2
    pure (tau,code)
  else none

/-- Original source-universe decoding with a context-independent result type. -/
def rawUniverseDecode (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (value : Nat) : Option (RawPacked n) :=
  bif rawCarrierTest n arity symbols S Gamma value then rawPackedDecode n arity Gamma value else none

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecoding
