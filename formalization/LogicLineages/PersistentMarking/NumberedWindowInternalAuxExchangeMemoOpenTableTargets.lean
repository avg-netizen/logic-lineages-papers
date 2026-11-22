module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableTargets
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalRawListRecursion (lookup)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalAuxExchangeMemoTargets (selected)
open NumberedWindowInternalSparseFieldParser (scratchRow scratchTable)
open NumberedWindowInternalSparsePair (pairTerm)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)

abbrev readRow {α : Type} (R : Program 4) (out key : OTerm α) : Formula α :=
  programGraph (scratchRow (constantZero 2) R) out ![key,z,z]

abbrev tableAt {α : Type} (R : Program 4) (out key : OTerm α) : Formula α :=
  programGraph (scratchTable (constantZero 2) R) out ![key,z,z]

abbrev updateAt {α : Type} (R : Program 4) (out key old : OTerm α) : Formula α :=
  programGraph R out ![key,old,z,z]

/-- The exact selected graph has the physical scratch row at the actual sparse pair. -/
def ExactOpenSelectedMemoProjection : Prop :=
  ∀ (R : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out a b : OTerm α),
    Nonempty (Derivation body Γ (programGraph (selected R) out ![a,b])) ↔
    Nonempty (Derivation body Γ (readRow R out (pairTerm a b)))

/-- Advance one row using the supplied graph of the same actual prior table and step. -/
def ExactOpenSelectedMemoSuccessor : Prop :=
  ∀ (R : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out key old : OTerm α),
    Nonempty (Derivation body Γ (tableAt R old key)) →
    Nonempty (Derivation body Γ (updateAt R out key old)) →
    Nonempty (Derivation body Γ (readRow R out (suc key)))

/-- A real additive offset retrieves the same earlier row from the supplied table. -/
def ExactOpenSelectedMemoLookup : Prop :=
  ∀ (R : Program 4) (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (out key offset old : OTerm α),
    Nonempty (Derivation body Γ (readRow R out key)) →
    Nonempty (Derivation body Γ (tableAt R old (OrdinaryArithmetic.addTerm key offset))) →
    Nonempty (Derivation body Γ (programGraph lookup out ![offset,old]))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxExchangeMemoOpenTableTargets
