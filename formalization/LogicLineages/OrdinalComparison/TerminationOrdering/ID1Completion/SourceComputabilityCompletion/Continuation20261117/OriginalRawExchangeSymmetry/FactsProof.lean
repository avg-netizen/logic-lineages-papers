module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.BindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLayerCalibration.InternalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.FactsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof BindingProof
open WindowSourceHeadInclusion.ClosureSyntaxProof (closureRename)
structure Facts (n : Nat) (arity : Fin n → Nat)
    (source target node rev window symbols types : OTerm alpha) : Prop where
  pair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target))
  reversePair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rev target source))
  windowPair : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types))
  sourceCode : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) source))
  targetCode : Nonempty (Derivation body Delta (graph1 (OriginalCodeValidityGuard.check n) (suc z) target))
  closed : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types))
  exchange : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window))
variable {n : Nat} {arity : Fin n → Nat}
variable {source target node rev window symbols types : OTerm alpha}
theorem Facts.toFields (h : Facts (body := body) (Delta := Delta) n arity source target node rev window symbols types) :
    Nonempty (Derivation body Delta (fields n arity source target node rev window symbols types)) :=
  andIntro h.pair (andIntro h.reversePair (andIntro h.windowPair
    (andIntro h.sourceCode (andIntro h.targetCode (andIntro h.closed h.exchange)))))
theorem ofFields (h : Nonempty (Derivation body Delta (fields n arity source target node rev window symbols types))) :
    Facts (body := body) (Delta := Delta) n arity source target node rev window symbols types :=
  ⟨andLeft h,andLeft (andRight h),andLeft (andRight (andRight h)),
   andLeft (andRight (andRight (andRight h))),andLeft (andRight (andRight (andRight (andRight h)))),
   andLeft (andRight (andRight (andRight (andRight (andRight h))))),
   andRight (andRight (andRight (andRight (andRight (andRight h)))))⟩
theorem Facts.rename (h : Facts (body := body) (Delta := Delta) n arity source target node rev window symbols types)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Facts (body := body) (Delta := Theta) n arity (source.relabel j) (target.relabel j)
      (node.relabel j) (rev.relabel j) (window.relabel j) (symbols.relabel j) (types.relabel j) := by
  apply ofFields
  have hh := renameInto h.toFields j Theta hj
  rw [fieldsRename] at hh
  exact hh
theorem Facts.weaken (h : Facts (body := body) (Delta := Delta) n arity source target node rev window symbols types)
    (Theta : List (Formula alpha)) (hi : ∀ q ∈ Delta, q ∈ Theta) :
    Facts (body := body) (Delta := Theta) n arity source target node rev window symbols types :=
  ofFields (InternalApplicationValidityStackAppendFrameQueryProof.weakenProof h.toFields hi)
theorem reverseGuard (h : Facts (body := body) (Delta := Delta) n arity source target node rev window symbols types) :
    Nonempty (Derivation body Delta (graph3 (OriginalDecodedLayerCalibration.guard n) (suc z) rev z window)) := by
  have hg := OriginalDecodedLambdaRecurrence.SuccessProof.guardNecessary n arity node window h.exchange
  have hfields := (OriginalDecodedLayerCalibration.InternalProof.internalGuard n body alpha Delta
    node z window source target symbols types h.pair h.windowPair).mp hg
  exact (OriginalDecodedLayerCalibration.InternalProof.internalGuard n body alpha Delta
    rev z window target source symbols types h.reversePair h.windowPair).mpr
    (andIntro (andIntro h.targetCode h.sourceCode) (andRight hfields))
theorem childReverse (parent left right child reversed window symbols types : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity parent)))
    (small : Nonempty (Derivation body Delta (InternalLessThan.strictLess left parent)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing child left right)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing reversed right left)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)))
    (hc : Nonempty (Derivation body Delta (WindowSourceHeadInclusion.ArrowClosed types)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) child window))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) reversed window)) := by
  have guards := OriginalExchangeBoundsPreservation.ExchangeGuardProof.accepted n arity child left right window hp he
  exact belowRawApply n arity parent left right child reversed window symbols types ih small
    (Facts.toFields ⟨hp,hr,hw,andLeft guards,andRight guards,hc,he⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.FactsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.FactsProof
