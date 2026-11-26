module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeChildQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeQueriesProof
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
def first (n : Nat) (i : Fin 3) : Program 4 := .composition (ExchangeChildQueriesProof.queries n i) ![.projection 0,.projection 2]
def last (n : Nat) (i : Fin 3) : Program 4 := .composition (ExchangeChildQueriesProof.queries n i) ![.projection 1,.projection 3]
def queries (n : Nat) : Fin 6 → Program 4 := ![first n 0,first n 1,first n 2,last n 0,last n 1,last n 2]
open Continuation20261115

theorem recover (n : Nat) (lc ld rc rd : OTerm alpha) (ys : Fin 6 → OTerm alpha)
    (hq : ∀ i, Nonempty (Derivation body Delta (programGraph (queries n i) (ys i) ![lc,ld,rc,rd]))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 0) lc rc)) ∧
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw (ys 1) lc)) ∧
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw (ys 2) rc)) ∧
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing (ys 3) ld rd)) ∧
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw (ys 4) ld)) ∧
    Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw (ys 5) rd)) := by
  have hf : ∀ i, Nonempty (Derivation body Delta (programGraph (ExchangeChildQueriesProof.queries n i) (![ys 0,ys 1,ys 2] i) ![lc,rc])) := by
    intro i
    fin_cases i
    · exact binaryRecover (ExchangeChildQueriesProof.queries n 0) (.projection 0) (.projection 2) (ys 0) lc rc ![lc,ld,rc,rd] (hq 0) (projectionValue 0 ![lc,ld,rc,rd]) (projectionValue 2 ![lc,ld,rc,rd])
    · exact binaryRecover (ExchangeChildQueriesProof.queries n 1) (.projection 0) (.projection 2) (ys 1) lc rc ![lc,ld,rc,rd] (hq 1) (projectionValue 0 ![lc,ld,rc,rd]) (projectionValue 2 ![lc,ld,rc,rd])
    · exact binaryRecover (ExchangeChildQueriesProof.queries n 2) (.projection 0) (.projection 2) (ys 2) lc rc ![lc,ld,rc,rd] (hq 2) (projectionValue 0 ![lc,ld,rc,rd]) (projectionValue 2 ![lc,ld,rc,rd])
  have ht : ∀ i, Nonempty (Derivation body Delta (programGraph (ExchangeChildQueriesProof.queries n i) (![ys 3,ys 4,ys 5] i) ![ld,rd])) := by
    intro i
    fin_cases i
    · exact binaryRecover (ExchangeChildQueriesProof.queries n 0) (.projection 1) (.projection 3) (ys 3) ld rd ![lc,ld,rc,rd] (hq 3) (projectionValue 1 ![lc,ld,rc,rd]) (projectionValue 3 ![lc,ld,rc,rd])
    · exact binaryRecover (ExchangeChildQueriesProof.queries n 1) (.projection 1) (.projection 3) (ys 4) ld rd ![lc,ld,rc,rd] (hq 4) (projectionValue 1 ![lc,ld,rc,rd]) (projectionValue 3 ![lc,ld,rc,rd])
    · exact binaryRecover (ExchangeChildQueriesProof.queries n 2) (.projection 1) (.projection 3) (ys 5) ld rd ![lc,ld,rc,rd] (hq 5) (projectionValue 1 ![lc,ld,rc,rd]) (projectionValue 3 ![lc,ld,rc,rd])
  obtain ⟨hp,hl,hr⟩ := ExchangeChildQueriesProof.recover n lc rc ![ys 0,ys 1,ys 2] hf
  obtain ⟨hq',hl',hr'⟩ := ExchangeChildQueriesProof.recover n ld rd ![ys 3,ys 4,ys 5] ht
  exact ⟨hp,hl,hr,hq',hl',hr'⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeQueriesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.BinaryExchangeQueriesProof
