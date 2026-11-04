module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingTargets
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedNumericDecoding
open NumberedNumericCarrier NumberedUniformPackedDecoding

def ActualRawStructuralCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (raw : RawPacked n),
    rawStructuralDecode arity Gamma raw = (decodePacked arity Gamma raw).map packedCode

def ActualRawStructuralDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × RawPacked n => rawStructuralDecode arity p.1 p.2)

def ActualRawPackedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat),
    rawPackedDecode n arity Gamma value = (decodePackedNumber n arity Gamma value).map packedCode

def ActualRawPackedDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × Nat => rawPackedDecode n arity p.1 p.2)

def ActualRawUniverseCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty) (value : Nat),
    rawUniverseDecode n arity symbols S Gamma value =
      (decodeUniverse n arity symbols S Gamma value).map packedCode

def ActualRawUniverseDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × List Ty × Nat =>
      rawUniverseDecode n arity p.1.1 p.1.2 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformPackedDecodingTargets
