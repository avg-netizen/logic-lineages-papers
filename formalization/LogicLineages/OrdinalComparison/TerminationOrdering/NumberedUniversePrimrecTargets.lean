module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecTargets
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedRewriteReduction
open NumberedNumericCarrier

def ActualTermUniverseSuccessPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × (List Ty × Ty × Code (Fin n)) =>
      (decodeTerm arity p.2.1 p.2.2.1 p.2.2.2).any (universeTest p.1.1 p.1.2))

def ActualArgumentsUniverseSuccessPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × (List Ty × List Ty × Code (Fin n)) =>
      (decodeArguments arity p.2.1 p.2.2.1 p.2.2.2).any (argumentsUniverseTest p.1.1 p.1.2))

def ActualRawCarrierPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × List Ty × Nat =>
      rawCarrierTest n arity p.1.1 p.1.2 p.2.1 p.2.2)

def ActualPackedUniversePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Packed (Fin n) arity Gamma =>
      universeTest p.1.1 p.1.2 p.2.2)

def ActualUniverseDecoderPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) × Nat =>
      decodeUniverse n arity p.1.1 p.1.2 Gamma p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecTargets
