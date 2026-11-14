module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric NumberedLeastCodeRepresentative

def NativeRawWindow : Prop := ∀ (n : Nat) (symbols : List (Fin n)) (types : List Source.Ty),
  evaluate rawWindow (List.Vector.ofFn ![numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
    numbersNumber ((NumberedFiniteUniverse.rawHeadWindow symbols types).map
      (fun head => headNumber (NumberedAuxiliaryCoding.headCode head)))

def NativeSourceHeads : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (types : List Source.Ty),
  (evaluate (sourceHeads n arity) (List.Vector.ofFn ![numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
    numbersNumber ((NumberedAuxiliaryEnumeration.sourceHeads arity symbols types).map headNumber)) ∧
  (∀ head : NumberedAuxiliaryCoding.HeadCode (Fin n),
    evaluate (member n arity) (List.Vector.ofFn ![headNumber head,numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
      (decide (head ∈ NumberedAuxiliaryEnumeration.sourceHeads arity symbols types)).toNat)

def InternalFilterNil : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 (filterHeads n arity) (numeral 0) (numeral 0) symbols types))

def InternalFilterCons : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (list head tail rest symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)) →
  Nonempty (Derivation body Delta (graph3 (filterHeads n arity) rest tail symbols types)) →
  (Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 0) head symbols types)) →
    Nonempty (Derivation body Delta (graph3 (filterHeads n arity) rest list symbols types))) ∧
  (∀ out : OTerm alpha,
    Nonempty (Derivation body Delta (graph3 (OriginalHeadWindow.window n arity) (numeral 1) head symbols types)) →
    Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out head rest)) →
    Nonempty (Derivation body Delta (graph3 (filterHeads n arity) out list symbols types)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalSourceHeads.Targets
