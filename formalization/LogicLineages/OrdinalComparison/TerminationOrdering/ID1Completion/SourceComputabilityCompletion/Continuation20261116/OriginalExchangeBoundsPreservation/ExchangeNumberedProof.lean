module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.UnaryExchangeAtProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeGuardProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedLambdaRecurrence.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.OrdinaryExchangeCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedWindowProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedProof
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
    (left right label otherLabel lh rh lt rt lts rts lc ld rc rd node window lv rv : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor left ![label,lh,lt,lc,lts,ld])))
    (hrc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor right ![otherLabel,rh,rt,rc,rts,rd])))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalDecodedRank.SupportProof.pairCases window _
  intro beta j Theta symbols types hj hw
  rw [eqnRelabel]
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hlcj hrcj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,belowRawRename] at hpj hej hlvj hrvj ihj
  exact ExchangeNumberedWindowProof.preserved n arity (left.relabel j) (right.relabel j)
    (label.relabel j) (otherLabel.relabel j) (lh.relabel j) (rh.relabel j) (lt.relabel j) (rt.relabel j) (lts.relabel j) (rts.relabel j)
    (lc.relabel j) (ld.relabel j) (rc.relabel j) (rd.relabel j) (node.relabel j)
    (window.relabel j) symbols types (lv.relabel j) (rv.relabel j)
    hlcj hrcj hpj hej hlvj hrvj hw ihj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedProof
