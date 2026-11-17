module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.LeafStableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.SelectorsStableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open DataDefinitions CompositionStableProof

theorem context (n : Nat) (arity : Fin n → Nat) : Stable n arity OriginalClassCodes.context :=
  unary n arity InternalUnpair.left (.projection 1) (LeafStableProof.parameter n arity)
theorem gamma (n : Nat) (arity : Fin n → Nat) : Stable n arity OriginalClassCodes.gamma :=
  unary n arity InternalUnpair.right (.projection 1) (LeafStableProof.parameter n arity)
theorem window (n : Nat) (arity : Fin n → Nat) : Stable n arity OriginalClassCodes.window :=
  unary n arity InternalUnpair.left OriginalClassCodes.context (context n arity)
theorem symbols (n : Nat) (arity : Fin n → Nat) : Stable n arity OriginalClassCodes.symbols :=
  unary n arity InternalUnpair.left OriginalClassCodes.window (window n arity)
theorem types (n : Nat) (arity : Fin n → Nat) : Stable n arity OriginalClassCodes.types :=
  unary n arity InternalUnpair.right OriginalClassCodes.window (window n arity)
theorem bound (n : Nat) (arity : Fin n → Nat) : Stable n arity OriginalClassCodes.bound :=
  unary n arity OriginalContextInsertion.length OriginalClassCodes.gamma (gamma n arity)
theorem size (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.size n) :=
  unary n arity InternalUnpair.left (OriginalClassCodes.bounds n) (LeafStableProof.bounds n arity)
theorem labels (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.labels n) :=
  unary n arity InternalUnpair.right (OriginalClassCodes.bounds n) (LeafStableProof.bounds n arity)
theorem fuel (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.fuel n) :=
  binary n arity InternalArithmeticPrograms.addition (OriginalClassCodes.size n) (OriginalClassCodes.size n)
    (size n arity) (size n arity)
theorem heads (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.heads n arity) :=
  unary n arity (InternalListMap.map OriginalHeadEncodingBridge.encodeHead)
    (.composition (OriginalSourceHeads.sourceHeads n arity) ![OriginalClassCodes.symbols,OriginalClassCodes.types])
    (binary n arity (OriginalSourceHeads.sourceHeads n arity) OriginalClassCodes.symbols OriginalClassCodes.types
      (symbols n arity) (types n arity))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.SelectorsStableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.SelectorsStableProof
