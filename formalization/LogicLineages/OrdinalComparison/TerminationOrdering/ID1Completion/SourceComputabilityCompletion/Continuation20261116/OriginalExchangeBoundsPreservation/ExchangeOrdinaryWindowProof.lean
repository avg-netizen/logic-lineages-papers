module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryExchangeAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OrdinaryExchangeCasesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeOrdinaryWindowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115.OriginalBoundsRecombination (maximum merge)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (z suc eqn sucRelabel zRelabel eqnRelabel)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open ExchangeInduction ExchangeInductionSyntaxProof
open Continuation20261115

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc rc node window symbols types lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor left lm lc)))
    (hrc : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor right rm rc)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (ExchangeChildQueriesProof.queries n) ![lc,rc] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![lc,rc] i).relabel j) = ![lc.relabel j,rc.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [eqnRelabel]
  obtain ⟨hchild,hcv,hdv⟩ := ExchangeChildQueriesProof.recover n (lc.relabel j) (rc.relabel j) ys hq
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  have hwj := renameInto hw j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,belowRawRename] at hlcj hrcj hpj hej hlvj hrvj hwj ihj
  exact OrdinaryExchangeCasesProof.atValues n arity (left.relabel j) (right.relabel j)
    (lm.relabel j) (rm.relabel j) (lc.relabel j) (rc.relabel j) (node.relabel j)
    (ys 0) (window.relabel j) (symbols.relabel j) (types.relabel j) (ys 1) (ys 2)
    (lv.relabel j) (rv.relabel j) hlcj hrcj hpj hchild hwj hej hcv hdv hlvj hrvj ihj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeOrdinaryWindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeOrdinaryWindowProof
