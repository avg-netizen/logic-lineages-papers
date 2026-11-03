module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeCodeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPackedCodecPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedExchangeCode

/-- Exact original neighborhood membership on all typed inputs and windows. -/
def ActualPackedCalibration : Prop :=
  ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (Gamma : List Ty) (symbols : List Symbol) (S : List Ty)
    (q r : Packed Symbol arity Gamma),
    packedCodeExchange arity symbols S (packedCode q) (packedCode r) =
      NumberedExchangeNeighborhood.exchangeTest symbols S q r

/-- The structural checker is primitive recursive on every pair of raw codes. -/
def ActualCodeExchangePrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × Code (Fin n) × Code (Fin n) =>
      codeExchange arity p.1.1 p.1.2 p.2.1 p.2.2)

/-- The original Boolean exchange test, jointly in windows and both packed terms. -/
def ActualExchangeTestPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
    Primrec (fun p : (List (Fin n) × List Ty) ×
        Packed (Fin n) arity Gamma × Packed (Fin n) arity Gamma =>
      NumberedExchangeNeighborhood.exchangeTest p.1.1 p.1.2 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangePrimrecTargets
