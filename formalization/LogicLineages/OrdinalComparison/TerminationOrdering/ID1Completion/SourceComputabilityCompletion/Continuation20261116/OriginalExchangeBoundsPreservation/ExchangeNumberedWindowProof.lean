module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.NumberedExchangeCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.BinaryExchangeQueriesProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedWindowProof
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
open OriginalRawSyntaxTransport (numberedConstructor)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSupportProof (symm)

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right label otherLabel lh rh lt rt lts rts lc ld rc rd node window symbols types lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph numberedConstructor left ![label,lh,lt,lc,lts,ld])))
    (hrc : Nonempty (Derivation body Delta (programGraph numberedConstructor right ![otherLabel,rh,rt,rc,rts,rd])))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (hw : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing window symbols types)))
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
  have hwj := renameInto hw j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hlcj hrcj
  simp only [graph1Rename,graph2Rename,graph3Rename,sucRelabel,zRelabel,belowRawRename] at hpj hej hlvj hrvj hwj ihj
  have hr := (OriginalDecodedNumberedRecurrence.Proof.numberedRecurrence n arity body beta Theta
    (left.relabel j) (right.relabel j) (label.relabel j) (otherLabel.relabel j)
    (lh.relabel j) (rh.relabel j) (lt.relabel j) (rt.relabel j)
    (lc.relabel j) (rc.relabel j) (lts.relabel j) (rts.relabel j) (ld.relabel j) (rd.relabel j)
    (node.relabel j) (ys 0) (ys 3) (window.relabel j) (symbols.relabel j) (types.relabel j)
    hlcj hrcj hpj hfirst hlast hwj).mp hej
  obtain ⟨hlabel⟩ := andLeft (andLeft (andRight hr))
  have hrc' := headTransport numberedConstructor (right.relabel j) (otherLabel.relabel j) (label.relabel j)
    ![rh.relabel j,rt.relabel j,rc.relabel j,rts.relabel j,rd.relabel j] ⟨symm hlabel⟩ hrcj
  exact NumberedExchangeCasesProof.atValues n arity (left.relabel j) (right.relabel j) (label.relabel j)
    (lh.relabel j) (rh.relabel j) (lt.relabel j) (rt.relabel j) (lts.relabel j) (rts.relabel j)
    (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j) (node.relabel j) (ys 0) (ys 3)
    (window.relabel j) (symbols.relabel j) (types.relabel j) (ys 1) (ys 2) (ys 4) (ys 5)
    (lv.relabel j) (rv.relabel j) hlcj hrc' hpj hfirst hlast hwj hej hcv hdv hev hfv hlvj hrvj ihj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedWindowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedWindowProof
