module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationTargets
open Source NumberedAuxiliaryDecoding NumberedNumericDecoding NumberedNumericTypedValidation

def ActualNumericTermValidation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) (value : Nat),
    termValid n arity Gamma tau value =
      ((decodeCode n value).bind (decodeTerm arity Gamma tau)).isSome

def ActualNumericArgumentsValidation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma types : List Ty) (value : Nat),
    argumentsValid n arity Gamma types value =
      ((decodeCode n value).bind (decodeArguments arity Gamma types)).isSome

def ActualNumericPackedValidation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat),
    packedValid n arity Gamma value = (decodePackedNumber n arity Gamma value).isSome

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationTargets
