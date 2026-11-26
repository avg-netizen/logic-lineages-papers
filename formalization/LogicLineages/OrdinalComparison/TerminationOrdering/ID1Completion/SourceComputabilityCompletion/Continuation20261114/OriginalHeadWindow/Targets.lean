module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric NumberedLeastCodeRepresentative

def NativeArity : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (s : Fin n) (symbols types : Nat),
  evaluate (arityAt n arity) (List.Vector.ofFn ![s.val,symbols,types]) = arity s

def NativeWindow : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (types : List Source.Ty) (head : NumberedAuxiliaryCoding.HeadCode (Fin n)),
  evaluate (window n arity) (List.Vector.ofFn ![headNumber head,
    numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
    (decide (NumberedFiniteUniverse.HeadInWindow arity symbols types
      (NumberedAuxiliaryDecoding.decodeHead head))).toNat

/-- Exact arithmetic factor at actual raw pair, not semantic head decoding. -/
def InternalBranch : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (tag : Fin 6)
    (raw payload symbols types out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral tag.val) payload)) →
  (Nonempty (Derivation body Delta (graph3 (window n arity) out raw symbols types)) ↔
   Nonempty (Derivation body Delta (graph3 (branchWindow n arity tag.val) out payload symbols types)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadWindow.Targets
