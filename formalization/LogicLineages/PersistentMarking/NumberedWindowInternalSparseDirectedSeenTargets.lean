module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric (decodeNumbers)
open NumberedWindowInternalSparseDirectedSeen

/-- The local original advance test, with an explicit edge AST and literal
standard scratch decoding. Reject absent scratch decoding and nil; test
each occurrence of the actual ordered list without changing it. -/
def ExactAllInputDirectedSeen : Prop :=
  ∀ (E : Program 4) (seen ctx ty v : Nat),
    evaluate (scan E) (List.Vector.ofFn (scanTape seen ctx ty v)) =
      ((decodeNumbers seen).any (fun pool => pool.any (fun w =>
        (w == v) || decide (evaluate E (List.Vector.ofFn (edgeTape ctx ty w v)) = 1)))).toNat

/-- A successful physical scan yields an internal witness on the same
seen code and candidate, without a numerical edge or membership premise. -/
def ExactOpenDirectedSeenWitness : Prop :=
  ∀ (E : Program 4) (body : Positive (Fin 1)) (α : Type)
    (Γ : List (Formula α)) (seen ctx ty v : OTerm α),
    Nonempty (Derivation body Γ ((scanGraph E seen ctx ty v).imp (seenWitness E seen ctx ty v)))

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedSeenTargets
