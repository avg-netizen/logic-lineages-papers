module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalRawSyntaxTransport OriginalStructuralNodeSize
open InternalAdditionLawsProof (add)
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- No native value is used as an internal graph premise. -/
def NativeCalibration : Prop :=
  (∀ state : Nat, evaluate OriginalStructuralNodeSize.transition (List.Vector.ofFn ![state]) =
    OriginalStructuralNodeSize.transitionValue state) ∧
  (∀ input : Nat, evaluate raw (List.Vector.ofFn ![input]) = rawValue input) ∧
  (∀ input : Nat, evaluate packed (List.Vector.ofFn ![input]) = rawValue (Nat.unpair input).2) ∧
  (∀ (n : Nat) (q : Code (Fin n)), evaluate raw (List.Vector.ofFn ![codeNumber q]) = nodeCount q)

/-- Independent native syntax identity, not graph reflection. -/
def NativeErasureInvariant : Prop := ∀ (n : Nat) (q : Code (Fin n)) (sigma : Source.Ty) (cutoff : Nat),
  nodeCount (eraseCode sigma cutoff q) = nodeCount q

/-- Complete raw leaf/unary/binary recurrence, including unknown-tag leaves.
These are the literal arity/child selectors of the original machine. -/
def InternalLeaf : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 (arityOf (.projection 0)) z input).imp (graph1 raw (suc z) input)))
def InternalUnary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input child count : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 (arityOf (.projection 0)) (suc z) input ⊓
      (graph1 (firstOf (.projection 0)) child input ⊓ graph1 raw count child)).imp
      (graph1 raw (suc count) input)))
def InternalBinary : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input first second firstCount secondCount : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 (arityOf (.projection 0)) (suc (suc z)) input ⊓
      (graph1 (firstOf (.projection 0)) first input ⊓
       (graph1 (secondOf (.projection 0)) second input ⊓
        (graph1 raw firstCount first ⊓ graph1 raw secondCount second)))).imp
      (graph1 raw (suc (add firstCount secondCount)) input)))
def InternalErasureInvariant : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input erased typ cutoff before after : InternalGraphComposition.OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph3 eraseRaw erased typ cutoff input ⊓
      (graph1 raw before input ⊓ graph1 raw after erased)).imp (equal before after)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeTargets
