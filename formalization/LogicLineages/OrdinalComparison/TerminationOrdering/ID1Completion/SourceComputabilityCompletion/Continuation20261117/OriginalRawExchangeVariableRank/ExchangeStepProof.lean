module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ActiveDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserUnaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalDecodedRank.SupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeStepProof
open Continuation20261114 Continuation20261115 Continuation20261116
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open ExchangeInduction ExchangeInductionSyntaxProof Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem preserved (n : Nat) (arity : Fin n → Nat)
    (left right node window lv rv : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node left right)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) node window)))
    (hlv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw lv left)))
    (hrv : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.variableRankRaw rv right)))
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (eqn lv rv)) := by
  apply OriginalDecodedRank.SupportProof.pairCases left _
  intro beta j Theta st sp hj hl
  rw [eqnRelabel]
  have hpj := renameInto hp j Theta hj
  have hej := renameInto he j Theta hj
  have hlvj := renameInto hlv j Theta hj
  have hrvj := renameInto hrv j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,belowRawRename] at hpj hej hlvj hrvj ihj
  apply OriginalDecodedRank.SupportProof.pairCases (right.relabel j) _
  intro gamma k Xi tt tp hk hr
  rw [eqnRelabel]
  have hpk := renameInto hpj k Xi hk
  have hek := renameInto hej k Xi hk
  have hlvk := renameInto hlvj k Xi hk
  have hrvk := renameInto hrvj k Xi hk
  have ihk := renameInto ihj k Xi hk
  have hlk := renameInto hl k Xi hk
  rw [graph2Rename] at hlk
  simp only [graph1Rename,graph2Rename,sucRelabel,zRelabel,belowRawRename] at hpk hek hlvk hrvk ihk
  have hs := OriginalDecodedSuccessShape.CoreProof.successShape n arity
    ((node.relabel j).relabel k) ((left.relabel j).relabel k) ((right.relabel j).relabel k)
    (st.relabel k) (sp.relabel k) tt tp ((window.relabel j).relabel k) hpk hlk hr hek
  exact ActiveDispatchProof.preserved n arity ((left.relabel j).relabel k) ((right.relabel j).relabel k)
    ((node.relabel j).relabel k) ((window.relabel j).relabel k) ((lv.relabel j).relabel k) ((rv.relabel j).relabel k)
    (st.relabel k) tt (pairLeft _ _ _ hlk) (pairLeft _ _ _ hr) (andLeft hs) (andRight hs) hpk hek hlvk hrvk ihk
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeVariableRank.ExchangeStepProof
