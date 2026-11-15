module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.InductionDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)

def fields {alpha : Type} (n : Nat) (raw fuel1 bound1 table1 fuel2 bound2 table2 : OTerm alpha) : Formula alpha :=
  ((InternalLessThan.strictLess raw (suc bound1) ⊓ InternalLessThan.strictLess raw (suc bound2)) ⊓
    (InternalLessThan.strictLess raw fuel1 ⊓ InternalLessThan.strictLess raw fuel2)) ⊓
  ((graph2 (OriginalCodeDecoderTable.tableProgram n) table1 fuel1 bound1 ⊓
    graph2 (OriginalCodeDecoderTable.tableProgram n) table2 fuel2 bound2) ⊓
    graph2 InternalRawListRecursion.lookup (suc z) raw table1)
def result {alpha : Type} (n : Nat) (raw fuel1 bound1 table1 fuel2 bound2 table2 : OTerm alpha) : Formula alpha :=
  graph2 InternalRawListRecursion.lookup (suc z) raw table2
def matrix {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula (alpha ⊕ Fin 6) :=
  (fields n (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5))).imp
  (result n (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
    (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)))
def AtRaw {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix n raw)
def rawPredicate {alpha : Type} (n : Nat) : Formula (alpha ⊕ Fin 1) := AtRaw n (.var (.inr 0))
def BelowRaw {alpha : Type} (n : Nat) (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate n) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.InductionDefinitions
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityCoherence.InductionDefinitions
