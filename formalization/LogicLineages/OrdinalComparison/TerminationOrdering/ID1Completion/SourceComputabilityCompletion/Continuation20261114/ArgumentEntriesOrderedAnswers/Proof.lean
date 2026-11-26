module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.ListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalAcceptanceSupportProof InternalApplicationCertificateConstructorsSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem atDeps (raw tau head tail param deps table left right answers depTail actualDeps : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table head)))
    (hr : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table tail)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps table)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depTail tail z)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode actualDeps head depTail))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup left z answers) ⊓
       (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))) := by
  have hchildren := ArgumentEntriesChildren.InternalProof.internalBinary body alpha Delta true raw tau head tail depTail actualDeps hc ht hk
  have hactual : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency actualDeps raw param)) :=
    unaryValue ArgumentEntriesChildren.children (.projection 0) actualDeps raw (Fin.cons raw (Fin.cons param Fin.elim0))
      hchildren (projectionValue 0 (Fin.cons raw (Fin.cons param Fin.elim0)))
  have he := valueUnique ArgumentEntriesRecursor.dependency actualDeps deps (Fin.cons raw (Fin.cons param Fin.elim0)) hactual hd
  have hk' := outputTransport InternalListCodec.consCode actualDeps deps (Fin.cons head (Fin.cons depTail Fin.elim0)) he hk
  exact ListProof.twoResult deps depTail head tail table left right answers ht hk' hl hr hm
theorem atTail (raw tau head tail param deps table left right answers depTail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table head)))
    (hr : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table tail)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps table)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode depTail tail z))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup left z answers) ⊓
       (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons depTail Fin.elim0)) _
  intro beta j Theta actualDeps hj hx
  change Nonempty (Derivation body Theta
    (((graph2 InternalRawListRecursion.lookup left z answers).relabel j) ⊓
     ((graph2 InternalRawListRecursion.lookup right (numeral 1) answers).relabel j)))
  simp only [graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hcj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hmj
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at htj
  exact atDeps (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (deps.relabel j) (table.relabel j) (left.relabel j) (right.relabel j) (answers.relabel j) (depTail.relabel j) actualDeps hcj hdj hlj hrj hmj htj hx
theorem consResult (raw tau head tail param deps table left right answers : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor raw tau head tail)))
    (hd : Nonempty (Derivation body Delta (graph2 ArgumentEntriesRecursor.dependency deps raw param)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table head)))
    (hr : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table tail)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers deps table))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup left z answers) ⊓
       (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))) := by
  apply programCases InternalListCodec.consCode (Fin.cons tail (Fin.cons z Fin.elim0)) _
  intro beta j Theta depTail hj hx
  change Nonempty (Derivation body Theta
    (((graph2 InternalRawListRecursion.lookup left z answers).relabel j) ⊓
     ((graph2 InternalRawListRecursion.lookup right (numeral 1) answers).relabel j)))
  simp only [graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have hcj := renameInto hc j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hcj
  have hdj := renameInto hd j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hdj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hrj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,graph3Rename,zRelabel,sucRelabel] at hmj
  exact atTail (raw.relabel j) (tau.relabel j) (head.relabel j) (tail.relabel j) (param.relabel j) (deps.relabel j) (table.relabel j) (left.relabel j) (right.relabel j) (answers.relabel j) depTail hcj hdj hlj hrj hmj hx
theorem consAnswers : Targets.InternalConsAnswers := by
  intro body alpha Delta raw tau head tail param deps table left right answers hc hd hl hr hm
  have h := consResult raw tau head tail param deps table left right answers hc hd hl hr hm
  exact ⟨andLeft h, andRight h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Proof
