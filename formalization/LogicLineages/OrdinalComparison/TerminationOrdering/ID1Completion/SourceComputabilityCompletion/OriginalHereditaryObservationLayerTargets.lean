module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalHereditaryObservationLayer
open OriginalHereditaryObservationSourceUniformityTargets
open Source
def Native : Prop := ∀ R Q (v : List.Vector Nat 2),
  evaluate (layer R Q) v = Nat.pair (evaluate (OriginalRootObservation.rootObservation R) v)
    (Nat.pair (evaluate (OriginalRootObservation.rootObservation Q) v)
      (evaluate (OriginalHereditaryDeletionRows.rows Q) v))
def SourcePreservation : Prop := ∀ R Q n arity symbols S c,
  SubtypeClosed (fun t => t ∈ S) →
  SourceUniform R n arity symbols S c → SourceUniform Q n arity symbols S c →
  SourceUniform (layer R Q) n arity symbols S c
/-- Exact internal pairing/projection law. Literal branch and pair graphs only;
no native calibration, source-class oracle, or hereditary conclusion. -/
def Internal : Prop := ∀ R Q (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (input parameter out inner a b c : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 InternalPairing.pairing out a inner ⊓ graph2 InternalPairing.pairing inner b c).imp
      ((graph2 (layer R Q) out input parameter).iff
        (graph2 (OriginalRootObservation.rootObservation R) a input parameter ⊓
          (graph2 (OriginalRootObservation.rootObservation Q) b input parameter ⊓
            graph2 (OriginalHereditaryDeletionRows.rows Q) c input parameter)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerTargets
