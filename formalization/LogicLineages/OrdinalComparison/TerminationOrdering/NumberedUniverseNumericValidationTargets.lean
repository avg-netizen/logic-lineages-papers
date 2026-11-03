module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidationTargets
open Source NumberedAuxiliaryDecoding NumberedNumericDecoding NumberedNumericCarrier
open NumberedUniverseNumericValidation

def ActualNumericTermValidation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (tau : Ty) (value : Nat),
    termValid n arity symbols S Gamma tau value =
      ((decodeCode n value).bind (decodeTerm arity Gamma tau)).any (universeTest symbols S)

def ActualNumericArgumentsValidation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma types : List Ty) (value : Nat),
    argumentsValid n arity symbols S Gamma types value =
      ((decodeCode n value).bind (decodeArguments arity Gamma types)).any
        (argumentsUniverseTest symbols S)

def ActualRawCarrierValidation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (value : Nat),
    packedValid n arity symbols S Gamma value = rawCarrierTest n arity symbols S Gamma value

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidationTargets
