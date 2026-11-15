module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Targets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
/-- All-raw internal acceptance coherence across independently bounded original
finite decoder tables, at any two sufficient fuels. Strict child descent,
positive-fuel predecessor witnesses and earlier-table observations are internal
proof duties, not hypotheses. This asserts acceptance equivalence, not equality
of arbitrary table outputs or whole supplier installation. -/
def InternalSufficientFuelCoherence : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (raw fuel1 bound1 table1 fuel2 bound2 table2 : OTerm alpha),
  Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc bound1))) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess raw (suc bound2))) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess raw fuel1)) →
  Nonempty (Derivation body Delta (InternalLessThan.strictLess raw fuel2)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalCodeDecoderTable.tableProgram n) table1 fuel1 bound1)) →
  Nonempty (Derivation body Delta
    (graph2 (OriginalCodeDecoderTable.tableProgram n) table2 fuel2 bound2)) →
  (Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) raw table1)) ↔
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup (suc z) raw table2)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Targets
