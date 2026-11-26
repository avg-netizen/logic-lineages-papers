module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.InputProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Every slot is an actual program on the unchanged [seed,parameter] input.
These are transient proof observations, not premises in the frozen endpoint. -/
def queries (n : Nat) (arity : Fin n → Nat) (H : Program 1) : Fin 13 → Program 2 :=
  ![rootType,types,heads n arity,size n,labels n,bound,fuel n,admitted n H,
    node n,parameter n arity,InputProof.metadataMiddle n arity,InputProof.metadataTail n,enumerated n arity]
structure Frame {alpha : Type} (n : Nat) (arity : Fin n → Nat) (H : Program 1)
    (body : Positive (Fin 1)) (Delta : List (Formula alpha)) (seed param : OTerm alpha) where
  values : Fin 13 → OTerm alpha
  graph : ∀ i, Nonempty (Derivation body Delta (graph2 (queries n arity H i) (values i) seed param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes
