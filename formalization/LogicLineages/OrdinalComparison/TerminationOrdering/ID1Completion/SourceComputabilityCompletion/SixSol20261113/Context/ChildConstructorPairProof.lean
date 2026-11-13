module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalConstructorSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorPairProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem applicationPair (raw domain child0 child1 children payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.applicationConstructor raw domain child0 child1)))
    (hchildren : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children child0 child1)))
    (hpayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 2) payload)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons domain (Fin.cons child0 (Fin.cons child1 Fin.elim0))
  let inner : Program 3 := pairOf (.projection 1) (.projection 2)
  let outer : Program 3 := pairOf (.projection 0) inner
  have hi := binaryValue InternalPairing.pairing (.projection 1) (.projection 2) children child0 child1 xs
    hchildren (projectionValue 1 xs) (projectionValue 2 xs)
  have ho := binaryValue InternalPairing.pairing (.projection 0) inner payload domain children xs
    hpayload (projectionValue 0 xs) hi
  exact binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 2) outer
    raw (numeral 2) payload xs hc (constantValue 2 xs) ho

theorem consPair (raw domain child0 child1 children payload : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw domain child0 child1)))
    (hchildren : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing children child0 child1)))
    (hpayload : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload domain children))) :
    Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) payload)) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons domain (Fin.cons child0 (Fin.cons child1 Fin.elim0))
  let inner : Program 3 := pairOf (.projection 1) (.projection 2)
  let outer : Program 3 := pairOf (.projection 0) inner
  have hi := binaryValue InternalPairing.pairing (.projection 1) (.projection 2) children child0 child1 xs
    hchildren (projectionValue 1 xs) (projectionValue 2 xs)
  have ho := binaryValue InternalPairing.pairing (.projection 0) inner payload domain children xs
    hpayload (projectionValue 0 xs) hi
  exact binaryRecover InternalPairing.pairing (OriginalRawSyntaxTransport.constant 3 7) outer
    raw (numeral 7) payload xs hc (constantValue 7 xs) ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorPairProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ChildConstructorPairProof
