module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.CompositionStableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.LeafStableProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalTagArithmeticSupportProof (symm)
open DataDefinitions
attribute [local irreducible] programGraph

theorem fixedValue {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
    (P : Program 2) (seed candidate parameter out value : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (graph2 P value seed parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 P value candidate parameter)))
    (h : Nonempty (Derivation body Delta (graph2 P out seed parameter))) :
    Nonempty (Derivation body Delta (graph2 P out candidate parameter)) := by
  obtain ⟨he⟩ := valueUnique P out value ![seed,parameter] h hs
  exact outputTransport P value out ![candidate,parameter] ⟨symm he⟩ ht

theorem parameter (n : Nat) (arity : Fin n → Nat) : Stable n arity (.projection 1) := by
  intro body alpha Delta seed candidate parameter out d h
  exact fixedValue (.projection 1) seed candidate parameter out parameter
    (projectionValue 1 ![seed,parameter]) (projectionValue 1 ![candidate,parameter]) h

theorem zero (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalRawSyntaxTransport.constant 2 0) :=
  CompositionStableProof.composition n arity .zero Fin.elim0 (fun i => Fin.elim0 i)

theorem rootType (n : Nat) (arity : Fin n → Nat) : Stable n arity OriginalClassCodes.rootType := by
  intro body alpha Delta seed candidate parameter out d h
  have hs := unaryValue InternalUnpair.left (.projection 0) d.root seed ![seed,parameter]
    (pairLeft seed d.root d.left d.sourcePair) (projectionValue 0 ![seed,parameter])
  have ht := unaryValue InternalUnpair.left (.projection 0) d.root candidate ![candidate,parameter]
    (pairLeft candidate d.root d.right d.targetPair) (projectionValue 0 ![candidate,parameter])
  exact fixedValue OriginalClassCodes.rootType seed candidate parameter out d.root hs ht h

theorem bounds (n : Nat) (arity : Fin n → Nat) : Stable n arity (OriginalClassCodes.bounds n) := by
  intro body alpha Delta seed candidate parameter out d h
  have sl := unaryValue InternalUnpair.right (.projection 0) d.left seed ![seed,parameter]
    (pairRight seed d.root d.left d.sourcePair) (projectionValue 0 ![seed,parameter])
  have tr := unaryValue InternalUnpair.right (.projection 0) d.right candidate ![candidate,parameter]
    (pairRight candidate d.root d.right d.targetPair) (projectionValue 0 ![candidate,parameter])
  have hs := unaryValue (OriginalCodeBoundsRecursion.bounds n) OriginalClassCodes.seedRaw
    d.bounds d.left ![seed,parameter] d.sourceBounds sl
  have ht := unaryValue (OriginalCodeBoundsRecursion.bounds n) OriginalClassCodes.seedRaw
    d.bounds d.right ![candidate,parameter] d.targetBounds tr
  exact fixedValue (OriginalClassCodes.bounds n) seed candidate parameter out d.bounds hs ht h

theorem admitted (n : Nat) (arity : Fin n → Nat) :
    Stable n arity (OriginalClassCodes.admitted n (OriginalConcreteHeadSignature.signature n arity)) := by
  intro body alpha Delta seed candidate parameter out d h
  exact fixedValue (OriginalClassCodes.admitted n (OriginalConcreteHeadSignature.signature n arity))
    seed candidate parameter out (numeral 1) d.sourceAdmitted d.targetAdmitted h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.LeafStableProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.LeafStableProof
