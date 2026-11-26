module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteDropProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalListCodecSupportProof InternalRecursionClosureLogicProof
open OriginalClassContextAllPositionObserver OriginalAllPositionContextDeleteFrontSyntaxProof
open OriginalAllPositionContextDeleteBaseProof OriginalAllPositionContextDeleteFrontStepProof
open OriginalAllPositionContextDeleteDropProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem successorReady (count gamma head tail result out previous d singleton oldFull : InternalGraphComposition.OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front result (suc count) tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head result)))
    (hv : Nonempty (Derivation body Delta (graph2 front previous count tail)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d count tail)))
    (hs : Nonempty (Derivation body Delta (consGraph singleton d z)))
    (hf : Nonempty (Derivation body Delta (consGraph oldFull head previous)))
    : Nonempty (Derivation body Delta (graph2 front out (suc (suc count)) gamma)) := by
  have hi := rowApply count gamma head tail previous oldFull hrow hc hv hf
  have ha := frontAppendRecover count previous tail d singleton result hv hp hl hs
  have hb := InternalApplicationValidityStackAppendListProof.consBackward
    oldFull head previous singleton result out hf ha ho
  obtain ⟨he⟩ := lookupConsIff gamma head tail count d hc
  obtain ⟨hl⟩ := hl
  have hl' := Nonempty.intro (Derivation.implicationElimination (Derivation.conjunctionRight he) hl)
  exact frontNext (suc count) oldFull gamma d singleton out hi hl' hs hb

theorem successorWithSingleton (count gamma head tail result out previous d singleton : InternalGraphComposition.OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front result (suc count) tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head result)))
    (hv : Nonempty (Derivation body Delta (graph2 front previous count tail)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d count tail)))
    (hs : Nonempty (Derivation body Delta (consGraph singleton d z)))
    : Nonempty (Derivation body Delta (graph2 front out (suc (suc count)) gamma)) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons previous Fin.elim0)) _
  intro beta j Theta oldFull hj hnew
  simp only [graph2Rename,sucRelabel]
  have hrow' := renameInto hrow j Theta hj
  rw [rowRename] at hrow'
  have hc' := renameInto hc j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc'
  have hp' := renameInto hp j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hp'
  have ho' := renameInto ho j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at ho'
  have hv' := renameInto hv j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hv'
  have hl' := renameInto hl j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hl'
  have hs' := renameInto hs j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel,zRelabel] at hs'
  simp only [consTermRename,emptyRename,zRelabel] at hnew
  exact successorReady (count.relabel j) (gamma.relabel j) (head.relabel j) (tail.relabel j) (result.relabel j) (out.relabel j) (previous.relabel j) (d.relabel j) (singleton.relabel j) oldFull hrow' hc' hp' ho' hv' hl' hs' hnew

theorem successorWithLookup (count gamma head tail result out previous d : InternalGraphComposition.OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front result (suc count) tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head result)))
    (hv : Nonempty (Derivation body Delta (graph2 front previous count tail)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d count tail)))
    : Nonempty (Derivation body Delta (graph2 front out (suc (suc count)) gamma)) := by
  apply programCases InternalListCodec.consCode (Fin.cons d (Fin.cons z Fin.elim0)) _
  intro beta j Theta singleton hj hnew
  simp only [graph2Rename,sucRelabel]
  have hrow' := renameInto hrow j Theta hj
  rw [rowRename] at hrow'
  have hc' := renameInto hc j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc'
  have hp' := renameInto hp j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hp'
  have ho' := renameInto ho j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at ho'
  have hv' := renameInto hv j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hv'
  have hl' := renameInto hl j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hl'
  simp only [consTermRename,emptyRename,zRelabel] at hnew
  exact successorWithSingleton (count.relabel j) (gamma.relabel j) (head.relabel j) (tail.relabel j) (result.relabel j) (out.relabel j) (previous.relabel j) (d.relabel j) singleton hrow' hc' hp' ho' hv' hl' hnew

theorem successorWithPrevious (count gamma head tail result out previous : InternalGraphComposition.OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front result (suc count) tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head result)))
    (hv : Nonempty (Derivation body Delta (graph2 front previous count tail)))
    : Nonempty (Derivation body Delta (graph2 front out (suc (suc count)) gamma)) := by
  apply programCases InternalRawListRecursion.lookup (Fin.cons count (Fin.cons tail Fin.elim0)) _
  intro beta j Theta d hj hnew
  simp only [graph2Rename,sucRelabel]
  have hrow' := renameInto hrow j Theta hj
  rw [rowRename] at hrow'
  have hc' := renameInto hc j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc'
  have hp' := renameInto hp j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hp'
  have ho' := renameInto ho j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at ho'
  have hv' := renameInto hv j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hv'
  simp only [consTermRename,emptyRename,zRelabel] at hnew
  exact successorWithLookup (count.relabel j) (gamma.relabel j) (head.relabel j) (tail.relabel j) (result.relabel j) (out.relabel j) (previous.relabel j) d hrow' hc' hp' ho' hv' hnew

theorem succCore (count gamma head tail result out : InternalGraphComposition.OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count)))
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front result (suc count) tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head result)))
    : Nonempty (Derivation body Delta (graph2 front out (suc (suc count)) gamma)) := by
  apply programCases front (Fin.cons count (Fin.cons tail Fin.elim0)) _
  intro beta j Theta previous hj hnew
  simp only [graph2Rename,sucRelabel]
  have hrow' := renameInto hrow j Theta hj
  rw [rowRename] at hrow'
  have hc' := renameInto hc j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hc'
  have hp' := renameInto hp j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at hp'
  have ho' := renameInto ho j Theta hj
  simp only [consGraphRename,graph2Rename,sucRelabel] at ho'
  simp only [consTermRename,emptyRename,zRelabel] at hnew
  exact successorWithPrevious (count.relabel j) (gamma.relabel j) (head.relabel j) (tail.relabel j) (result.relabel j) (out.relabel j) previous hrow' hc' hp' ho' hnew

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontCoreProof
