module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedMultisetNumeric NumberedLeastCodeRepresentative

def NativeHeadMove : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (types : List Source.Ty)
    (f g : NumberedAuxiliaryCoding.HeadCode (Fin n)) (base target : NumberedAuxiliaryCoding.Code (Fin n)),
  evaluate (headMove n arity) (List.Vector.ofFn ![headNumber f,codeNumber base,headNumber g,codeNumber target,
    numbersNumber (symbols.map Fin.val),numbersNumber (types.map typeNumber)]) =
      (NumberedExchangeCode.headMove arity symbols types f base g target).toNat

/-- No native semantics: acceptance factors into four actual arithmetic graph facts. -/
def InternalAcceptance : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (f base g target symbols types : OTerm alpha),
  (Nonempty (Derivation body Delta (programGraph (headMove n arity) (numeral 1) ![f,base,g,target,symbols,types])) ↔
   Nonempty (Derivation body Delta
     (((graph3 (OriginalHeadWindow.window n arity) (numeral 1) f symbols types ⊓
        graph3 (OriginalSourceHeads.member n arity) (numeral 1) g symbols types) ⊓
       graph2 OriginalHeadClass.equivalent (numeral 1) f g) ⊓
      graph2 OriginalArgumentPermutation.check (numeral 1) base target)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.OriginalHeadMove.Targets
