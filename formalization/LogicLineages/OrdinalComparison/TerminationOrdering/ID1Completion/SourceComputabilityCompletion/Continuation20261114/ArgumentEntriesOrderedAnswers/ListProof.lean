module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesConsTable.ConsSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.ListProof
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

theorem atLists (keys tail first second table left right answers rest out : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys first tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table first)))
    (hr : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table second)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers keys table)))
    (hc1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z)))
    (hc0 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode out left rest))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup left z answers) ⊓
       (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))) := by
  have hmt := ArgumentEntriesConsTable.MapProof.present body alpha Delta tail second z table right z rest ht hr
    (ArgumentEntriesNilExtraction.LeafSupportProof.mapNil table) hc1
  have hmo := ArgumentEntriesConsTable.MapProof.present body alpha Delta keys first tail table left rest out hk hl hmt hc0
  have he := valueUnique ExchangeMapGraph.mapGraph out answers (Fin.cons keys (Fin.cons table Fin.elim0)) hmo hm
  have hc := outputTransport InternalListCodec.consCode out answers (Fin.cons left (Fin.cons rest Fin.elim0)) he hc0
  have hd0 := InternalRawListRecursionSupportProof.dropZero (body := body) (Gamma := Delta) answers
  have hd1 := InternalRawListRecursionSupportProof.dropNext rest answers z answers hd0
    (InternalRawListRecursionSupportProof.consTail answers left rest hc)
  exact andIntro
    (InternalRawListRecursionSupportProof.lookupValue left z answers answers hd0
      (InternalRawListRecursionSupportProof.consHead answers left rest hc))
    (InternalRawListRecursionSupportProof.lookupValue right (numeral 1) answers rest hd1
      (InternalRawListRecursionSupportProof.consHead rest right z hc1))
theorem atRest (keys tail first second table left right answers rest : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys first tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table first)))
    (hr : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table second)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers keys table)))
    (hc1 : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode rest right z))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup left z answers) ⊓
       (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))) := by
  apply programCases InternalListCodec.consCode (Fin.cons left (Fin.cons rest Fin.elim0)) _
  intro beta j Theta out hj hx
  change Nonempty (Derivation body Theta
    (((graph2 InternalRawListRecursion.lookup left z answers).relabel j) ⊓
     ((graph2 InternalRawListRecursion.lookup right (numeral 1) answers).relabel j)))
  simp only [graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at htj
  have hkj := renameInto hk j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hkj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hrj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hmj
  have hc1j := renameInto hc1 j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hc1j
  exact atLists (keys.relabel j) (tail.relabel j) (first.relabel j) (second.relabel j) (table.relabel j) (left.relabel j) (right.relabel j) (answers.relabel j) (rest.relabel j) out htj hkj hlj hrj hmj hc1j hx
theorem twoResult (keys tail first second table left right answers : OTerm alpha)
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tail second z)))
    (hk : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode keys first tail)))
    (hl : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc left) table first)))
    (hr : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.lookup (suc right) table second)))
    (hm : Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph answers keys table))) :
    Nonempty (Derivation body Delta
      ((graph2 InternalRawListRecursion.lookup left z answers) ⊓
       (graph2 InternalRawListRecursion.lookup right (numeral 1) answers))) := by
  apply programCases InternalListCodec.consCode (Fin.cons right (Fin.cons z Fin.elim0)) _
  intro beta j Theta rest hj hx
  change Nonempty (Derivation body Theta
    (((graph2 InternalRawListRecursion.lookup left z answers).relabel j) ⊓
     ((graph2 InternalRawListRecursion.lookup right (numeral 1) answers).relabel j)))
  simp only [graph2Rename,zRelabel,GuardedSourceSyntaxProof.numeralRename]
  simp only [consTermRename,emptyRename,zRelabel] at hx
  have htj := renameInto ht j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at htj
  have hkj := renameInto hk j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hkj
  have hlj := renameInto hl j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hlj
  have hrj := renameInto hr j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hrj
  have hmj := renameInto hm j Theta hj
  simp only [graph2Rename,zRelabel,sucRelabel] at hmj
  exact atRest (keys.relabel j) (tail.relabel j) (first.relabel j) (second.relabel j) (table.relabel j) (left.relabel j) (right.relabel j) (answers.relabel j) rest htj hkj hlj hrj hmj hx
theorem twoAnswers : Targets.InternalTwoAnswers := by
  intro body alpha Delta keys tail first second table left right answers ht hk hl hr hm
  have h := twoResult keys tail first second table left right answers ht hk hl hr hm
  exact ⟨andLeft h, andRight h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.ListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesOrderedAnswers.ListProof
