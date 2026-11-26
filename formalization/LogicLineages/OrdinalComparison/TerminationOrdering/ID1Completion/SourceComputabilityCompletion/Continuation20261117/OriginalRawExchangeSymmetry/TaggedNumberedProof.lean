module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserNumberedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedNumberedProof
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
open Definitions FieldsSyntaxProof AllSyntaxProof SyntaxProof BindingProof FactsProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm trans)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
theorem reversed (n : Nat) (arity : Fin n → Nat)
    (left right node rev window symbols types : OTerm alpha)
    (hlt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) left)))
    (hrt : Nonempty (Derivation body Delta (graph1 OriginalRawSyntaxTransport.rawTag (numeral 5) right)))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases left _ hlt
  intro beta j Theta ll lh lt lc lts ld hj hlc
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hrtj := renameInto hrt j Theta hj
  have ihj := renameInto ih j Theta hj
  simp only [graph1Rename,GuardedSourceSyntaxProof.numeralRename] at hrtj
  rw [belowRawRename] at ihj
  have hh := h.rename j Theta hj
  apply OriginalRawSyntaxTransportInternalParserNumberedProof.numberedCases (right.relabel j) _ hrtj
  intro gamma k Xi rr rh rt rc rts rd hk hrc
  simp only [graph2Rename,sucRelabel,zRelabel]
  have ihk := renameInto ihj k Xi hk
  rw [belowRawRename] at ihk
  have hlck := renameInto hlc k Xi hk
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hlck
  exact NumberedProof.reversed n arity ((left.relabel j).relabel k) ((right.relabel j).relabel k)
    (ll.relabel k) rr (lh.relabel k) rh (lt.relabel k) rt (lc.relabel k) rc (lts.relabel k) rts (ld.relabel k) rd ((node.relabel j).relabel k) ((rev.relabel j).relabel k)
    ((window.relabel j).relabel k) ((symbols.relabel j).relabel k) ((types.relabel j).relabel k)
    hlck hrc (hh.rename k Xi hk) ihk

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedNumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.TaggedNumberedProof
