module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.TaggedConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeRejectionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeDispatchProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem tag1 (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (left right node window typ gamma context symbols types : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 1) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 1) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ right gamma context)) := by
  cases arguments
  · exact TaggedLambdaProof.preserved n arity left right node window typ gamma context symbols types hlt hrt henv hedge ih ha hp
  · exact ModeRejectionProof.argumentsTag n arity 1 (by decide) (by decide) left typ gamma context _ hlt ha

theorem tag2 (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (left right node window typ gamma context symbols types : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 2) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 2) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ right gamma context)) := by
  cases arguments
  · exact TaggedApplicationProof.preserved n arity left right node window typ gamma context symbols types hlt hrt henv hedge ih ha hp
  · exact ModeRejectionProof.argumentsTag n arity 2 (by decide) (by decide) left typ gamma context _ hlt ha

theorem tag4 (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (left right node window typ gamma context symbols types : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 4) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 4) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ right gamma context)) := by
  cases arguments
  · exact TaggedOrdinaryProof.preserved n arity left right node window typ gamma context symbols types hlt hrt henv hedge ih ha hp
  · exact ModeRejectionProof.argumentsTag n arity 4 (by decide) (by decide) left typ gamma context _ hlt ha

theorem tag5 (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (left right node window typ gamma context symbols types : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ right gamma context)) := by
  cases arguments
  · exact TaggedNumberedProof.preserved n arity left right node window typ gamma context symbols types hlt hrt henv hedge ih ha hp
  · exact ModeRejectionProof.argumentsTag n arity 5 (by decide) (by decide) left typ gamma context _ hlt ha

theorem tag7 (n : Nat) (arity : Fin n → Nat) (arguments : Bool)
    (left right node window typ gamma context symbols types : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 7) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 7) right)))
    (henv : Nonempty (Derivation body Delta (environment n context symbols types window)))
    (hedge : Nonempty (Derivation body Delta (edge n arity left right node window)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left)))
    (ha : Nonempty (Derivation body Delta (accepted n arity arguments typ left gamma context)))
    (hp : Nonempty (Derivation body Delta (plain n arity arguments typ right gamma))) :
    Nonempty (Derivation body Delta (accepted n arity arguments typ right gamma context)) := by
  cases arguments
  · exact ModeRejectionProof.termSeven n arity left typ gamma context _ hlt ha
  · exact TaggedConsProof.preserved n arity left right node window typ gamma context symbols types hlt hrt henv hedge ih ha hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeDispatchProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPlainAwareExchangeUniverse.ModeDispatchProof
