module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorTargets
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedNumericRoot
open NumberedUniformPackedDecoding NumberedUniformSelector

/-- Exact unguarded selector behavior on every actual typed endpoint pair. -/
def ActualSelectorCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (q r : Packed (Fin n) arity Gamma) (certificate : Nat),
    selectorCodeTest n arity symbols S Gamma table (packedCode q) (packedCode r) certificate =
      (decodeSelector n arity Gamma certificate).any
        (fun selector => selectorTest n arity symbols S Gamma table q r selector)

/-- Joint context, window, table, endpoint and certificate primitive recursiveness. -/
def ActualSelectorPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : (List (Fin n) × List Ty) × (Fin n → Fin n → Bool) ×
        List Ty × RawPacked n × RawPacked n × Nat =>
      selectorCodeTest n arity p.1.1 p.1.2 p.2.2.1 p.2.1
        p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniformSelectorTargets
