module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
/-- All raw vectors, original structuralValue and its decoder failure defaults. -/
def NativeStructural : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3),
  evaluate (structural n arity) v = TypedPrimaryEdge.structuralValue n arity v
/-- Exact installed E acceptance. Only original packed/parameter pair observations;
node and window graph witnesses are recovered internally, not public assumptions. -/
def InternalEdge : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target param tyA codeA tyB codeB ctx rest : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source tyA codeA)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target tyB codeB)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ctx rest)) →
  (Nonempty (Derivation body Delta (graph3 (edge n arity) (numeral 1) source target param)) ↔
   Nonempty (Derivation body Delta
    (eqn tyA tyB ⊓
      ((graph1 (OriginalDecodedContextValidity.contextGuard n) (numeral 1) ctx ⊓
        (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) codeA ⊓
         graph1 (OriginalCodeValidityGuard.check n) (numeral 1) codeB)) ⊓
       graph3 (atContext n arity) (numeral 1) codeA codeB ctx))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalConcreteStructuralEdge.Targets
