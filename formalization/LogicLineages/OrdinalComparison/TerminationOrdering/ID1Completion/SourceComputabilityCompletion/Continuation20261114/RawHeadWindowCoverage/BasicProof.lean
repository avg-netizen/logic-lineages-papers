module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.BasicProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SupportProof
attribute [local irreducible] programGraph

theorem basic : Targets.InternalBasic := by
  intro body alpha Delta which symbols types out head ho hp
  let xs : Fin 2 → OTerm alpha := ![symbols,types]
  have pairValue (tag : Nat)
      (h : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing head (numeral tag) (numeral 0)))) :
      Nonempty (Derivation body Delta (programGraph (pairOf (constant 2 tag) (constant 2 0)) head xs)) :=
    binaryValue InternalPairing.pairing (constant 2 tag) (constant 2 0) head (numeral tag) (numeral 0) xs h
      (constantValue tag xs) (constantValue 0 xs)
  revert hp
  refine Fin.cases ?_ (fun i => ?_) which
  · intro hp
    exact consHead _ _ out head xs (pairValue 0 hp) ho
  · refine Fin.cases ?_ (fun i => Fin.elim0 i) i
    intro hp
    exact secondHead _ _ _ out head xs (pairValue 1 hp) ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.BasicProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RawHeadWindowCoverage.BasicProof
