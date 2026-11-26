module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryObservationLayerInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsBoundProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionTransportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderInternalLogicSyntaxProof (equalRename)
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalClassContextAllPositionObserver (erasedPacked erasedParameter)
open OriginalHereditaryObservationLayer (layer)
open OriginalHereditaryDeletionRows (rows observation)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem indexedObservation (Q : Program 2)
    (input parameter gamma count row cutoff value : OTerm alpha)
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)))
    (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
    (hr : Nonempty (Derivation body Delta (graph2 (rows Q) row input parameter)))
    (hv : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup value cutoff row))) :
    Nonempty (Derivation body Delta (graph3 (observation Q) value cutoff input parameter)) := by
  obtain ⟨law⟩ := OriginalHereditaryDeletionRowsBoundProof.indexedRows
    Q body alpha Delta input parameter gamma count row cutoff value
  obtain ⟨args⟩ := andIntro hg (andIntro hl (andIntro hb (andIntro hr hv)))
  exact ⟨Derivation.implicationElimination law args⟩

/-- A shared ordered row is a shared key at every actually in-range deletion.
Its common cell is queried internally, without using an external evaluation. -/
theorem rowsReflect (Q : Program 2)
    (input parameter other otherParameter row cutoff gamma count otherGamma otherCount
      erased erasedParam otherErased otherErasedParam value otherValue : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (graph2 (rows Q) row input parameter)))
    (hor : Nonempty (Derivation body Delta (graph2 (rows Q) row other otherParameter)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hl : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length count gamma)))
    (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff count)))
    (hog : Nonempty (Derivation body Delta (graph1 InternalUnpair.right otherGamma otherParameter)))
    (hol : Nonempty (Derivation body Delta (graph1 OriginalContextInsertion.length otherCount otherGamma)))
    (hob : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff otherCount)))
    (he : Nonempty (Derivation body Delta (graph3 erasedPacked erased cutoff input parameter)))
    (hp : Nonempty (Derivation body Delta (graph3 erasedParameter erasedParam cutoff input parameter)))
    (hoe : Nonempty (Derivation body Delta (graph3 erasedPacked otherErased cutoff other otherParameter)))
    (hop : Nonempty (Derivation body Delta (graph3 erasedParameter otherErasedParam cutoff other otherParameter)))
    (hv : Nonempty (Derivation body Delta (graph2 Q value erased erasedParam)))
    (hov : Nonempty (Derivation body Delta (graph2 Q otherValue otherErased otherErasedParam))) :
    Nonempty (Derivation body Delta (equal value otherValue)) := by
  let xs : Fin 2 → OTerm alpha := Fin.cons cutoff (Fin.cons row Fin.elim0)
  apply programCases InternalRawListRecursion.lookup xs _
  intro beta j Theta cell hj hcell
  simp only [equalRename]
  have hx : (fun i => (xs i).relabel j) =
      Fin.cons (cutoff.relabel j) (Fin.cons (row.relabel j) Fin.elim0) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hx] at hcell
  have hr := renameInto hr j Theta hj
  have hor := renameInto hor j Theta hj
  have hg := renameInto hg j Theta hj
  have hl := renameInto hl j Theta hj
  have hb := renameInto hb j Theta hj
  have hog := renameInto hog j Theta hj
  have hol := renameInto hol j Theta hj
  have hob := renameInto hob j Theta hj
  have he := renameInto he j Theta hj
  have hp := renameInto hp j Theta hj
  have hoe := renameInto hoe j Theta hj
  have hop := renameInto hop j Theta hj
  have hv := renameInto hv j Theta hj
  have hov := renameInto hov j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename] at hr hor hg hl hog hol he hp hoe hop hv hov
  change Nonempty (Derivation body Theta
    ((InternalOriginalOrderSyntaxProof.ltF cutoff count).relabel j)) at hb
  change Nonempty (Derivation body Theta
    ((InternalOriginalOrderSyntaxProof.ltF cutoff otherCount).relabel j)) at hob
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hb hob
  have obs := indexedObservation Q (input.relabel j) (parameter.relabel j)
    (gamma.relabel j) (count.relabel j) (row.relabel j) (cutoff.relabel j) cell hg hl hb hr hcell
  have otherObs := indexedObservation Q (other.relabel j) (otherParameter.relabel j)
    (otherGamma.relabel j) (otherCount.relabel j) (row.relabel j) (cutoff.relabel j) cell hog hol hob hor hcell
  have q := binaryRecover Q erasedPacked erasedParameter cell
    (erased.relabel j) (erasedParam.relabel j)
    ![cutoff.relabel j,input.relabel j,parameter.relabel j] obs he hp
  have otherQ := binaryRecover Q erasedPacked erasedParameter cell
    (otherErased.relabel j) (otherErasedParam.relabel j)
    ![cutoff.relabel j,other.relabel j,otherParameter.relabel j] otherObs hoe hop
  have eqValue := valueUnique Q cell (value.relabel j)
    ![erased.relabel j,erasedParam.relabel j] q hv
  have shared := outputTransport Q cell (value.relabel j)
    ![otherErased.relabel j,otherErasedParam.relabel j] eqValue otherQ
  have result := valueUnique Q (value.relabel j) (otherValue.relabel j)
    ![otherErased.relabel j,otherErasedParam.relabel j] shared hov
  simpa only [equal,InternalSourceInversionSupportProof.onEquality,
    InternalTagArithmeticSyntaxProof.eqn] using result

/-- Recover the common deletion row from the genuine numeric key itself.
The second input uses precisely the queried first key's pair coordinates. -/
theorem layerDeletionTransport : Targets.LayerDeletionTransport := by
  intro R Q body alpha Delta input parameter other otherParameter key cutoff gamma count otherGamma otherCount
    erased erasedParam otherErased otherErasedParam value otherValue
    hk hok hg hl hb hog hol hob he hp hoe hop hv hov
  let A := OriginalRootObservation.rootObservation R
  let B := OriginalRootObservation.rootObservation Q
  let C := rows Q
  let inner := pairOf B C
  let qs : Fin 4 → Program 2 := ![A,B,C,inner]
  let xs : Fin 2 → OTerm alpha := Fin.cons input (Fin.cons parameter Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  simp only [equalRename]
  let xx : Fin 2 → OTerm beta := Fin.cons (input.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hx] at hq
  have hk := renameInto hk j Theta hj
  have hok := renameInto hok j Theta hj
  have hg := renameInto hg j Theta hj
  have hl := renameInto hl j Theta hj
  have hb := renameInto hb j Theta hj
  have hog := renameInto hog j Theta hj
  have hol := renameInto hol j Theta hj
  have hob := renameInto hob j Theta hj
  have he := renameInto he j Theta hj
  have hp := renameInto hp j Theta hj
  have hoe := renameInto hoe j Theta hj
  have hop := renameInto hop j Theta hj
  have hv := renameInto hv j Theta hj
  have hov := renameInto hov j Theta hj
  simp only [graph1Rename,graph2Rename,graph3Rename] at hk hok hg hl hog hol he hp hoe hop hv hov
  change Nonempty (Derivation body Theta
    ((InternalOriginalOrderSyntaxProof.ltF cutoff count).relabel j)) at hb
  change Nonempty (Derivation body Theta
    ((InternalOriginalOrderSyntaxProof.ltF cutoff otherCount).relabel j)) at hob
  rw [InternalOriginalOrderSyntaxProof.orderRename] at hb hob
  have outerPair := binaryRecover InternalPairing.pairing A inner
    (key.relabel j) (ys 0) (ys 3) xx hk (hq 0) (hq 3)
  have innerPair := binaryRecover InternalPairing.pairing B C
    (ys 3) (ys 1) (ys 2) xx (hq 3) (hq 1) (hq 2)
  have recovered := OriginalHereditaryObservationLayerInternalProof.recovery R Q
    (other.relabel j) (otherParameter.relabel j) (key.relabel j) (ys 3) (ys 0) (ys 1) (ys 2)
    outerPair innerPair hok
  exact rowsReflect Q (input.relabel j) (parameter.relabel j) (other.relabel j)
    (otherParameter.relabel j) (ys 2) (cutoff.relabel j) (gamma.relabel j) (count.relabel j)
    (otherGamma.relabel j) (otherCount.relabel j) (erased.relabel j) (erasedParam.relabel j)
    (otherErased.relabel j) (otherErasedParam.relabel j) (value.relabel j) (otherValue.relabel j)
    (hq 2) (andRight (andRight recovered)) hg hl hb hog hol hob he hp hoe hop hv hov

theorem familyDeletionTransport : Targets.FamilyDeletionTransport := by
  intro R depth
  exact layerDeletionTransport R (OriginalHereditaryFiniteObserver.family R depth)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionTransportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionTransportProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionTransportProof.layerDeletionTransport
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionTransportProof.familyDeletionTransport
