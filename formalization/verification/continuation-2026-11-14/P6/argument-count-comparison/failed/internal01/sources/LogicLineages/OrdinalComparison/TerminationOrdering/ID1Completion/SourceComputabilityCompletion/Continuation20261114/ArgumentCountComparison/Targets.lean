module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric

def NativeBounded : Prop := ∀ (candidates left right : List Nat),
  evaluate allCounts (List.Vector.ofFn ![numbersNumber candidates,numbersNumber left,numbersNumber right]) =
    (decide (∀ a ∈ candidates, left.count a = right.count a)).toNat

def NativePermutation : Prop :=
  (∀ (left right : List Nat), evaluate permutation
    (List.Vector.ofFn ![numbersNumber left,numbersNumber right]) = (decide (left.Perm right)).toNat) ∧
  (∀ (n : Nat) (left right : List (Source.Ty × NumberedAuxiliaryCoding.Code (Fin n))),
    evaluate permutation (List.Vector.ofFn ![numbersNumber (left.map Encodable.encode),numbersNumber (right.map Encodable.encode)]) =
      (decide (left.Perm right)).toNat)

def InternalNil : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 allCounts (numeral 1) (numeral 0) left right))

/-- Actual count graph premises identify outputs only, not semantic counts or extracted lists. -/
def InternalCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (list head tail left right lc rc : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count lc left head)) →
  Nonempty (Derivation body Delta (graph2 ArgumentEntryCount.count rc right head)) →
  (Nonempty (Derivation body Delta (graph3 allCounts (numeral 1) list left right)) ↔
   Nonempty (Derivation body Delta (eqn lc rc ⊓ graph3 allCounts (numeral 1) tail left right)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentCountComparison.Targets
