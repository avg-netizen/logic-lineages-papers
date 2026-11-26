module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeClassAndEquivalence : Prop :=
  (∀ (n : Nat) (h : NumberedAuxiliaryCoding.HeadCode (Fin n)),
    evaluate headClass (List.Vector.ofFn ![NumberedLeastCodeRepresentative.headNumber h]) =
      NumberedExchangeGuardsPrimrecProof.headClassNumber h) ∧
  (∀ (n : Nat) (f g : NumberedAuxiliaryCoding.HeadCode (Fin n)),
    evaluate equivalent (List.Vector.ofFn ![NumberedLeastCodeRepresentative.headNumber f,
      NumberedLeastCodeRepresentative.headNumber g]) =
    (decide (RecursiveComparison.headEquivalent (NumberedAuxiliaryDecoding.decodeHead f)
      (NumberedAuxiliaryDecoding.decodeHead g))).toNat)
def InternalTagFactor : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (tag : Fin 6) (raw payload out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag.val) payload)) →
  (Nonempty (Derivation body Delta (graph1 headClass out raw)) ↔
   Nonempty (Derivation body Delta (graph1 (branchClass tag.val) out payload)))
/-- Actual equality-test graph on actual class outputs, independent of calibration. -/
def InternalEquivalence : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (rawF rawG classF classG : OTerm alpha),
  Nonempty (Derivation body Delta (graph1 headClass classF rawF)) →
  Nonempty (Derivation body Delta (graph1 headClass classG rawG)) →
  (Nonempty (Derivation body Delta (graph2 equivalent (numeral 1) rawF rawG)) ↔
   Nonempty (Derivation body Delta (eqn classF classG)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadClass.Targets
