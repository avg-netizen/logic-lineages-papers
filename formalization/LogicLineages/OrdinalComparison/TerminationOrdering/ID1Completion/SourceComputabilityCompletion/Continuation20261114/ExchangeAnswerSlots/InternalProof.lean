module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.InstalledExchangeRecursor.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceNormalizationProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem constantGraph (k : Nat) (xs : Fin 3 → OTerm alpha) :
    Nonempty (Derivation body Delta (programGraph (constant k) (numeral k) xs)) := by
  induction k with
  | zero => exact constantZeroValue xs
  | succ k ih =>
    exact unaryValue .succ (constant k) (numeral (k+1)) (numeral k) xs
      (successorValue (Fin.cons (numeral k) Fin.elim0)) ih

theorem slotValue (k : Nat) (node code param value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (numeral k) code))) :
    Nonempty (Derivation body Delta (graph3 (rawSlot k) value node code param)) :=
  binaryValue InternalRawListRecursion.lookup (constant k) (.projection 1) value (numeral k) code
    ![node,code,param] h (constantGraph k ![node,code,param]) (projectionValue 1 ![node,code,param])

theorem slotFactor (k : Nat) (node code param value : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value (numeral k) code))) :
    (Nonempty (Derivation body Delta (graph3 (answer k) (numeral 1) node code param)) ↔
     Nonempty (Derivation body Delta (eqn value (numeral 1)))) := by
  have hv := slotValue k node code param value h
  constructor
  · intro ha
    have hr := normalizeRecover (rawSlot k) ![node,code,param] ha
    exact valueUnique (rawSlot k) value (numeral 1) ![node,code,param] hv hr
  · intro he
    have hr := outputTransport (rawSlot k) value (numeral 1) ![node,code,param] he hv
    exact normalizeAccept (rawSlot k) ![node,code,param] hr

theorem internalLeft : Targets.InternalLeft := by
  intro body alpha Delta node code param head tail hc
  have hh := InternalRawListRecursionSupportProof.consHead code head tail hc
  have hd := InternalRawListRecursionSupportProof.dropZero (body := body) (Gamma := Delta) code
  have hl := InternalRawListRecursionSupportProof.lookupValue head z code code hd hh
  exact slotFactor 0 node code param head hl

theorem internalRight : Targets.InternalRight := by
  intro body alpha Delta node code param h0 t0 h1 t1 h2 t2 h3 t3 hc0 hc1 hc2 hc3
  have hd0 := InternalRawListRecursionSupportProof.dropZero (body := body) (Gamma := Delta) code
  have hd1 := InternalRawListRecursionSupportProof.dropNext t0 code z code hd0
    (InternalRawListRecursionSupportProof.consTail code h0 t0 hc0)
  have hd2 := InternalRawListRecursionSupportProof.dropNext t1 t0 (suc z) code hd1
    (InternalRawListRecursionSupportProof.consTail t0 h1 t1 hc1)
  have hd3 := InternalRawListRecursionSupportProof.dropNext t2 t1 (suc (suc z)) code hd2
    (InternalRawListRecursionSupportProof.consTail t1 h2 t2 hc2)
  have hl := InternalRawListRecursionSupportProof.lookupValue h3 (numeral 3) code t2 hd3
    (InternalRawListRecursionSupportProof.consHead t2 h3 t3 hc3)
  exact slotFactor 3 node code param h3 hl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.InternalProof
