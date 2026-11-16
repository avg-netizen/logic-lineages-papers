module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.ExchangeNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedNumberedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open ExchangeInduction ExchangeInductionSyntaxProof Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right node window lv rv : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) right)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 (OriginalCodeBoundsRecursion.bounds n) rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases left _ hlt
  intro beta j Theta ll lh lt lc lts ld hj hlc
  rw [eqnRelabel]
  have hrtj := renameInto hrt j Theta hj
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,GuardedSourceSyntaxProof.numeralRename,belowRawRename] at hrtj hpj hej hlvj hrvj ihj
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases (right.relabel j) _ hrtj
  intro gamma k Xi rr rh rt rc rts rd hk hrc
  rw [eqnRelabel]
  have hpk := renameInto hpj k Xi hk
  have hek := renameInto hej k Xi hk
  have hlvk := renameInto hlvj k Xi hk
  have hrvk := renameInto hrvj k Xi hk
  have ihk := renameInto ihj k Xi hk
  have hlck := renameInto hlc k Xi hk
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hlck
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,belowRawRename] at hpk hek hlvk hrvk ihk
  exact ExchangeNumberedProof.preserved n arity ((left.relabel j).relabel k) ((right.relabel j).relabel k)
    (ll.relabel k) rr (lh.relabel k) rh (lt.relabel k) rt (lts.relabel k) rts (lc.relabel k) (ld.relabel k) rc rd ((node.relabel j).relabel k) ((window.relabel j).relabel k)
    ((lv.relabel j).relabel k) ((rv.relabel j).relabel k) hlck hrc hpk hek hlvk hrvk ihk
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalExchangeBoundsPreservation.TaggedNumberedProof
