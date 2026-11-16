module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariant
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open Continuation20261114
/-- Actual counts after deleting at most one occurrence. Equality of needle and
query is object-language equality, not an external decidable case or oracle. -/
def countEffect {alpha : Type} (raw needle rest bit : OTerm alpha) : Formula alpha :=
  let j : alpha → alpha ⊕ Fin 3 := Sum.inl
  let x : Fin 3 → OTerm (alpha ⊕ Fin 3) := fun i => .var (.inr i)
  InternalClosedPrograms.allBlock
    ((graph2 ArgumentEntryCount.count (x 1) (raw.relabel j) (x 0) ⊓
      graph2 ArgumentEntryCount.count (x 2) (rest.relabel j) (x 0)).imp
      (((eqn (needle.relabel j) (x 0)).imp
        (eqn (x 1) (OrdinaryArithmetic.addTerm (x 2) (bit.relabel j)))) ⊓
       ((eqn (needle.relabel j) (x 0)).not.imp (eqn (x 1) (x 2)))))
def fields {alpha : Type} (raw needle acc bit rest : OTerm alpha) : Formula alpha :=
  graph2 Erase.state acc raw needle ⊓ graph2 InternalPairing.pairing acc bit rest
def result {alpha : Type} (raw needle bit rest : OTerm alpha) : Formula alpha :=
  (eqn bit z ⊔ eqn bit (suc z)) ⊓ countEffect raw needle rest bit
def matrix {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 4) :=
  let x : Fin 4 → OTerm (alpha ⊕ Fin 4) := fun i => .var (.inr i)
  (fields (raw.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3)).imp
    (result (raw.relabel Sum.inl) (x 0) (x 2) (x 3))
def AtRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix raw)
def predicate {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw (.var (.inr 0))
def BelowRaw {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below predicate raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.EraseInvariant
