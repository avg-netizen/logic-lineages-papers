module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeCount : Prop :=
  (∀ (xs : List Nat) (needle : Nat),
    evaluate count (List.Vector.ofFn ![NumberedMultisetNumeric.numbersNumber xs,needle]) = xs.count needle) ∧
  (∀ (n : Nat) (xs : List (Source.Ty × NumberedAuxiliaryCoding.Code (Fin n))) (needle : Source.Ty × NumberedAuxiliaryCoding.Code (Fin n)),
    evaluate count (List.Vector.ofFn ![NumberedMultisetNumeric.numbersNumber (xs.map Encodable.encode),Encodable.encode needle]) =
      xs.count needle)
def InternalNil : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (needle : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 count (numeral 0) (numeral 0) needle))
def InternalEqualCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (list head tail needle acc : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)) →
  Nonempty (Derivation body Delta (graph2 count acc tail needle)) →
  Nonempty (Derivation body Delta (eqn head needle)) →
  Nonempty (Derivation body Delta (graph2 count (suc acc) list needle))
def InternalUnequalCons : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (list head tail needle acc : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)) →
  Nonempty (Derivation body Delta (graph2 count acc tail needle)) →
  Nonempty (Derivation body Delta (eqn head needle).not) →
  Nonempty (Derivation body Delta (graph2 count acc list needle))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntryCount.Targets
