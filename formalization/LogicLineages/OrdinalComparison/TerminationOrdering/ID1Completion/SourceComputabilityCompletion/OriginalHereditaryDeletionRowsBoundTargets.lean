module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryDeletionRows
/-- Exact total actual-length bounded row; arbitrary Q, including invalid vectors. -/
def NativeRows : Prop := ∀ (Q : Program 2) (input parameter : Nat),
  evaluate (rows Q) (List.Vector.ofFn ![input,parameter]) =
    NumberedMultisetNumeric.numbersNumber (values Q
      (evaluate OriginalContextInsertion.length (List.Vector.ofFn ![(Nat.unpair parameter).2])) input parameter)
/-- Same actual row with explicit original right-context and length graphs.
Only genuine graph/range premises, not a supplied recursion acceptance. -/
def IndexedRows : Prop := ∀ (Q : Program 2) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (input parameter gamma count row cutoff out : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 InternalUnpair.right gamma parameter ⊓
      (graph1 OriginalContextInsertion.length count gamma ⊓
        (OriginalContextInsertion.Below cutoff count ⊓
          (graph2 (rows Q) row input parameter ⊓
            graph2 InternalRawListRecursion.lookup out cutoff row)))).imp
      (graph3 (observation Q) out cutoff input parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundTargets
