module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.SelectorsStableProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.PipelineStableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open DataDefinitions CompositionStableProof
open SelectorsStableProof

theorem node (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.node n) :=
  binary n arity InternalPairing.pairing OriginalClassCodes.bound (OriginalClassCodes.fuel n)
    (bound n arity) (fuel n arity)
theorem tail (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.InputProof.metadataTail n) :=
  binary n arity InternalPairing.pairing (OriginalClassCodes.labels n) (OriginalClassCodes.size n)
    (labels n arity) (size n arity)
theorem middle (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.InputProof.metadataMiddle n arity) :=
  binary n arity InternalPairing.pairing (OriginalClassCodes.heads n arity) (OriginalClassCodes.InputProof.metadataTail n)
    (heads n arity) (tail n arity)
theorem parameter (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.parameter n arity) :=
  binary n arity InternalPairing.pairing OriginalClassCodes.types (OriginalClassCodes.InputProof.metadataMiddle n arity)
    (types n arity) (middle n arity)
theorem enumerated (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.enumerated n arity) :=
  binary n arity (OriginalEnumerationRecursion.enumeration n) (OriginalClassCodes.node n) (OriginalClassCodes.parameter n arity)
    (node n arity) (parameter n arity)
theorem frontend (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.frontend n arity) :=
  binary n arity OriginalClassCodes.pairRoots (OriginalClassCodes.enumerated n arity) OriginalClassCodes.rootType
    (enumerated n arity) (LeafStableProof.rootType n arity)
theorem classCodes (n : Nat) (arity : Fin n → Nat) :
    Stable n arity (OriginalClassCodes.classCodes n arity (OriginalConcreteHeadSignature.signature n arity)) :=
  ternary n arity LogicLineages.ComputabilityKnowledge.GorbowPRInternalControl.conditional
    (OriginalClassCodes.admitted n (OriginalConcreteHeadSignature.signature n arity))
    (OriginalRawSyntaxTransport.constant 2 0) (OriginalClassCodes.frontend n arity)
    (LeafStableProof.admitted n arity) (LeafStableProof.zero n arity) (frontend n arity)
theorem candidates (n : Nat) (arity : Fin n → Nat) :
    Stable n arity (OriginalCandidates.candidates n arity (OriginalConcreteHeadSignature.signature n arity)) :=
  binary n arity (OriginalCandidates.filterCandidates (OriginalConcreteHeadSignature.signature n arity))
    (OriginalClassCodes.classCodes n arity (OriginalConcreteHeadSignature.signature n arity)) OriginalClassCodes.gamma
    (classCodes n arity) (gamma n arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.PipelineStableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.PipelineStableProof
