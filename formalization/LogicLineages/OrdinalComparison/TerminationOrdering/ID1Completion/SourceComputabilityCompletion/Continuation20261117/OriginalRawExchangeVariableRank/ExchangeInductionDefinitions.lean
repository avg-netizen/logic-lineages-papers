module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.Definitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInduction
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc eqn)
open Continuation20261115
/-- Original source-raw induction. The target, actual packed node, unchanged
window and both actual variable ranks are universally quantified, not supplied oracles. -/
def fields {alpha : Type} (n : Nat) (arity : Fin n → Nat)
    (source target node window lv rv : OTerm alpha) : Formula alpha :=
  graph2 InternalPairing.pairing node source target ⊓
  (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window ⊓
    (graph1 OriginalRawSyntaxTransport.variableRankRaw lv source ⊓
     graph1 OriginalRawSyntaxTransport.variableRankRaw rv target))
def matrix {alpha : Type} (n : Nat) (arity : Fin n → Nat) (source : OTerm alpha) : Formula (alpha ⊕ Fin 5) :=
  let x : Fin 5 → OTerm (alpha ⊕ Fin 5) := fun i => .var (.inr i)
  (fields n arity (source.relabel Sum.inl) (x 0) (x 1) (x 2) (x 3) (x 4)).imp (eqn (x 3) (x 4))
def AtRaw {alpha : Type} (n : Nat) (arity : Fin n → Nat) (source : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (matrix n arity source)
def predicate {alpha : Type} (n : Nat) (arity : Fin n → Nat) : Formula (alpha ⊕ Fin 1) := AtRaw n arity (.var (.inr 0))
def BelowRaw {alpha : Type} (n : Nat) (arity : Fin n → Nat) (source : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (predicate n arity) source
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeInduction
