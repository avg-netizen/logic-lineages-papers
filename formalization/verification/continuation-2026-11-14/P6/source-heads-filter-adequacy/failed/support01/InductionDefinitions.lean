module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.Induction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors SourceComputabilityFormulaSupportProof
open TwoSol20261113.CalibratedPrimary.Membership

def result {alpha : Type} (raw symbols candidate types out value : OTerm alpha) : Formula alpha :=
  ((graph2 contains (numeral 1) out candidate).imp (qualifies raw candidate value)) ⊓
  ((qualifies raw candidate value).imp (graph2 contains (numeral 1) out candidate))
def fields (n : Nat) (arity : Fin n → Nat) {alpha : Type}
    (raw symbols candidate types out value : OTerm alpha) : Formula alpha :=
  graph3 (OriginalSourceHeads.filterHeads n arity) out raw symbols types ⊓
  graph3 (OriginalHeadWindow.window n arity) value candidate symbols types

def matrix (n : Nat) (arity : Fin n → Nat) {alpha : Type} (raw : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  (fields n arity (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4))).imp
    (result (raw.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)))
def AtRaw (n : Nat) (arity : Fin n → Nat) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalClosedPrograms.allBlock (matrix n arity raw)
def rawPredicate (n : Nat) (arity : Fin n → Nat) {alpha : Type} : Formula (alpha ⊕ Fin 1) := AtRaw n arity (.var (.inr 0))
def BelowRaw (n : Nat) (arity : Fin n → Nat) {alpha : Type} (raw : OTerm alpha) : Formula alpha := InternalStrongInduction.below (rawPredicate n arity) raw
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.Induction
