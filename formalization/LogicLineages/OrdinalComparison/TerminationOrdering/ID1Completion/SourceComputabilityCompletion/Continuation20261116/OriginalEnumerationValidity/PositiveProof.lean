module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.CombineClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.WitnessProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.ListClosureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.PositiveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalVariableSupportProof
open OriginalRawSyntaxTransportInternalConstructorFieldsProof OriginalRawSyntaxTransportInternalConstructorSelectorsProof
open InternalQuotientComparisonProof (orLeft orRight)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261115
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open OriginalEnumerationRecursionInterface
open InternalAcceptanceSupportProof
open InternalListCodecSupportProof InternalRawListRecursionSupportProof
open Lists ListSyntaxProof InductionSyntaxProof
theorem atKnown (n : Nat) (node param bound fuel ts hs ls tb p2 p3 out : OTerm alpha)
    (ih : Nonempty (Derivation body Delta (BelowRank n (suc fuel))))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node bound (suc fuel))))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param ts p2)))
    (h2 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p2 hs p3)))
    (h3 : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing p3 ls tb)))
    (he : Nonempty (Derivation body Delta (graph2 (OriginalEnumerationRecursion.enumeration n) out node param))) :
    Nonempty (Derivation body Delta (AllValid n out)) := by
  apply WitnessProof.cases n node param bound fuel _ hn
  intro beta j Theta ys hj hprior hopened hrest hdeps ha hb htail hvalues
  rw [allRename]
  have ihj := renameInto ih j Theta hj
  simp only [belowRankRename,InternalTagArithmeticSyntaxProof.sucRelabel] at ihj
  have hnj := renameInto hn j Theta hj
  have hpj := renameInto hp j Theta hj
  have h2j := renameInto h2 j Theta hj
  have h3j := renameInto h3 j Theta hj
  have hej := renameInto he j Theta hj
  simp only [graph2Rename,InternalTagArithmeticSyntaxProof.sucRelabel] at hnj hpj h2j h3j hej
  have hans := NodeProof.orderedAnswers n (node.relabel j) (param.relabel j) (bound.relabel j) (fuel.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5) (ys 6) (ys 7)
    hnj hprior hopened hrest hdeps ha hb htail hvalues
  have hg := (OriginalEnumerationEquation.Proof.exchangeEquation n body beta Theta
    (node.relabel j) (param.relabel j) (ys 7) (out.relabel j) hans).mp hej
  exact CombineClosureProof.positive n (node.relabel j) (param.relabel j) (bound.relabel j) (fuel.relabel j)
    (ts.relabel j) (hs.relabel j) (ls.relabel j) (tb.relabel j) (p2.relabel j) (p3.relabel j)
    (ys 4) (ys 5) (ys 6) (ys 7) (out.relabel j) hnj hpj h2j h3j htail hvalues
    (NodeProof.childValid n (fuel.relabel j) (bound.relabel j) (ys 0) (param.relabel j) (ys 4) ihj hprior ha)
    (NodeProof.childValid n (fuel.relabel j) (suc (bound.relabel j)) (ys 1) (param.relabel j) (ys 5) ihj hopened hb) hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.PositiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationValidity.PositiveProof
