module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalGuardedHeadEquality.StatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedNumberedRecurrence.StatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open Continuation20261114
open OriginalDecodedOrdinaryRecurrence (resultEqual)
/-- Original ordinary-head standalone recurrence with RAW head equality,
justified only after its actual guard is derived. The literal target/source
head-result test and actual headMove remain unchanged. -/
def InternalOrdinary : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target f g base dest node child param symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source f base)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor target g dest)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child base dest)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)) →
  (Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)) ↔
   Nonempty (Derivation body Delta
     (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param ⊓
       ((programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types] ⊓
          graph2 resultEqual (numeral 1) g f) ⊔
        (eqn f g ⊓
          graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) child param)))))

/-- Original numbered-head standalone recurrence with RAW head equality in
both alternatives, retaining exact metadata and left-associated disjunction. -/
def InternalNumbered : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (source target k l f g tau upsilon base dest ts us extras otherExtras
      node first last param symbols types : OTerm alpha),
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor source
    ![k,f,tau,base,ts,extras])) →
  Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor target
    ![l,g,upsilon,dest,us,otherExtras])) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing first base dest)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing last extras otherExtras)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)) →
  (Nonempty (Derivation body Delta
      (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) node param)) ↔
   Nonempty (Derivation body Delta
     (graph3 (OriginalDecodedLayerCalibration.guard n) (numeral 1) node z param ⊓
       ((eqn k l ⊓ (eqn tau upsilon ⊓ eqn ts us)) ⊓
         (((eqn extras otherExtras ⊓
             programGraph (OriginalHeadMove.headMove n arity) (numeral 1) ![f,base,g,dest,symbols,types]) ⊔
           ((eqn f g ⊓ eqn extras otherExtras) ⊓
             graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) first param)) ⊔
          ((eqn f g ⊓ eqn base dest) ⊓
            graph2 (OriginalDecodedExchangeEquation.exchange n arity) (numeral 1) last param))))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedHeadRecurrences.Targets
