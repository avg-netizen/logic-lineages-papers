module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ConcreteHeadMoveLayer.OrdinaryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.OrdinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open TwoSol20261113.CalibratedPrimary.Membership (contains)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalPositiveUnfoldingSupportProof InternalQuotientComparisonProof InternalBetaTotalityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem atEncoding (n : Nat) (arity : Fin n → Nat) (V : Program 3)
    (node code param source head base symbols types tail encoded : OTerm alpha)
    (hv : Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)))
    (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source source)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing param symbols types)))
    (hs : Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.ordinaryConstructor source head base)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code (numeral 1) tail)))
    (he : Nonempty (Derivation body Delta (graph1 OriginalHeadEncodingBridge.encodeHead encoded head))) :
    Nonempty (Derivation body Delta (graph3 (ConcreteHeadMoveLayer.layer n arity V) (numeral 2) node code param)) := by
  apply programCases OriginalHeadResult.headResult (Fin.cons head Fin.elim0) _
  intro beta j Theta result hj hr
  simp only [consTermRename,emptyRename] at hr
  have hvj := renameInto hv j Theta hj
  have hnj := renameInto hn j Theta hj
  have hpj := renameInto hp j Theta hj
  have hsj := renameInto hs j Theta hj
  have hcj := renameInto hc j Theta hj
  have hej := renameInto he j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hvj hnj hpj hsj hcj hej ⊢
  apply (ConcreteHeadMoveLayer.OrdinaryProof.internalOrdinary n arity body beta Theta V
    (node.relabel j) (code.relabel j) (param.relabel j) (source.relabel j) (source.relabel j)
    (head.relabel j) (head.relabel j) (base.relabel j) (base.relabel j) (encoded.relabel j) (encoded.relabel j)
    result result (symbols.relabel j) (types.relabel j) (numeral 1) (tail.relabel j)
    hvj hnj hpj hsj hsj hej hej hr hr hcj).mpr
  obtain ⟨hh⟩ := andIntro (show Nonempty (Derivation body Theta (eqn (encoded.relabel j) (encoded.relabel j))) from
    ⟨InternalTagArithmeticSupportProof.refl _⟩)
    (show Nonempty (Derivation body Theta (eqn (numeral 1) (numeral 1))) from ⟨InternalTagArithmeticSupportProof.refl _⟩)
  exact ⟨orRight hh⟩

theorem ordinary : Targets.InternalOrdinary := by
  intro n arity body alpha Delta V node code param source head base symbols types tail hv hn hp hs hc
  apply programCases OriginalHeadEncodingBridge.encodeHead (Fin.cons head Fin.elim0) _
  intro beta j Theta encoded hj he
  simp only [consTermRename,emptyRename] at he
  have hvj := renameInto hv j Theta hj
  have hnj := renameInto hn j Theta hj
  have hpj := renameInto hp j Theta hj
  have hsj := renameInto hs j Theta hj
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,GuardedSourceSyntaxProof.numeralRename] at hvj hnj hpj hsj hcj ⊢
  exact atEncoding n arity V (node.relabel j) (code.relabel j) (param.relabel j)
    (source.relabel j) (head.relabel j) (base.relabel j) (symbols.relabel j) (types.relabel j) (tail.relabel j)
    encoded hvj hnj hpj hsj hcj he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.OrdinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.RecursiveHeadLayerReflexivity.OrdinaryProof
