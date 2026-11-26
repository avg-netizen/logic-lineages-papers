module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.BinaryExchangeCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.BinaryExchangeQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeBinaryProof
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
open ExchangeInduction ExchangeInductionSyntaxProof
open Continuation20261115
open OriginalCodeBoundsConstructors.BinaryRootProof (constructor)

theorem preserved (cons : Bool) (n : Nat) (arity : Fin n → Nat)
    (left right lm rm lc ld rc rd node window lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (graph3 (constructor cons) left lm lc ld)))
    (hrc : Nonempty (Derivation body Delta (graph3 (constructor cons) right rm rc rd)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases (BinaryExchangeQueriesProof.queries n) ![lc,ld,rc,rd] _
  intro beta j ys Theta hj hq
  have hx : (fun i => (![lc,ld,rc,rd] i).relabel j) = ![lc.relabel j,ld.relabel j,rc.relabel j,rd.relabel j] := by
    funext i; fin_cases i <;> rfl
  rw [hx] at hq
  rw [eqnRelabel]
  obtain ⟨hfirst,hcv,hdv,hlast,hev,hfv⟩ := BinaryExchangeQueriesProof.recover n (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j) ys hq
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,belowRawRename] at hlcj hrcj hpj hej hlvj hrvj ihj
  exact BinaryExchangeCasesProof.atValues cons n arity (left.relabel j) (right.relabel j)
    (lm.relabel j) (rm.relabel j) (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j)
    (node.relabel j) (ys 0) (ys 3) (window.relabel j) (ys 1) (ys 2) (ys 4) (ys 5)
    (lv.relabel j) (rv.relabel j) hlcj hrcj hpj hfirst hlast hej hcv hdv hev hfv hlvj hrvj ihj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeBinaryProof
