module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedAtChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationDepth.BinaryValueProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedProof
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
open InternalTagArithmeticSupportProof (symm)
open InternalApplicationValidityStackAppendFrameQueryProof (weakenProof)
open OriginalRawSyntaxTransportInternalConstructorArityCasesProof (orCases)
open InternalQuotientComparisonProof (orLeft orRight)
theorem reversed (n : Nat) (arity : Fin n → Nat)
    (left right k l f g tau upsilon base dest ts us extras others node rev window symbols types : OTerm alpha)
    (hlc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor left ![k,f,tau,base,ts,extras])))
    (hrc : Nonempty (Derivation body Delta (programGraph OriginalRawSyntaxTransport.numberedConstructor right ![l,g,upsilon,dest,us,others])))
    (h : Facts (body := body) (Delta := Delta) n arity left right node rev window symbols types)
    (ih : Nonempty (Derivation body Delta (BelowRaw n arity left))) :
    Nonempty (Derivation body Delta (graph2 (OriginalDecodedExchangeEquation.exchange n arity) (suc z) rev window)) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases QueriesProof.binary ![base,extras,dest,others] _
  intro beta j ys Theta hj hq
  rw [QueriesProof.vector4Rename] at hq
  simp only [graph2Rename,sucRelabel,zRelabel]
  have hlcj := renameInto hlc j Theta hj
  have hrcj := renameInto hrc j Theta hj
  have ihj := renameInto ih j Theta hj
  rw [OriginalEnumerationDepth.BinaryValueProof.numberedRename] at hlcj hrcj
  rw [belowRawRename] at ihj
  obtain ⟨hp,hr,hq,hs⟩ := QueriesProof.binaryRecover (base.relabel j) (extras.relabel j) (dest.relabel j) (others.relabel j) ys hq
  exact NumberedAtChildrenProof.atChildren n arity (left.relabel j) (right.relabel j) (k.relabel j) (l.relabel j)
    (f.relabel j) (g.relabel j) (tau.relabel j) (upsilon.relabel j) (base.relabel j) (dest.relabel j)
    (ts.relabel j) (us.relabel j) (extras.relabel j) (others.relabel j) (node.relabel j) (rev.relabel j) (window.relabel j)
    (symbols.relabel j) (types.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) hlcj hrcj (h.rename j Theta hj) ihj hp hr hq hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalRawExchangeSymmetry.NumberedProof
