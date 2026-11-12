module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRawListRecursionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSyntaxProof
open InternalListCodecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryDeletionRows
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepValue (Q : Program 2) (index previous input parameter d singleton out : InternalGraphComposition.OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph3 (observation Q) d index input parameter)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton d z)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append out previous singleton))) :
    Nonempty (Derivation body Delta
      (programGraph (step Q) out (Fin.cons index (Fin.cons previous (Fin.cons input (Fin.cons parameter Fin.elim0)))))) := by
  let xs : Fin 4 → InternalGraphComposition.OTerm alpha := Fin.cons index (Fin.cons previous (Fin.cons input (Fin.cons parameter Fin.elim0)))
  let look : Program 4 := .composition (observation Q) ![.projection 0,.projection 2,.projection 3]
  let single : Program 4 := .composition InternalListCodec.consCode
    ![look,InternalAcceptance.constantZero 4]
  have hlook : Nonempty (Derivation body Delta (programGraph look d xs)) := by
    apply compositionValue (observation Q) ![.projection 0,.projection 2,.projection 3] d xs
      (Fin.cons index (Fin.cons input (Fin.cons parameter Fin.elim0))) hl
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k))) i
  have hsingle : Nonempty (Derivation body Delta (programGraph single singleton xs)) := by
    apply compositionValue InternalListCodec.consCode ![look,InternalAcceptance.constantZero 4]
      singleton xs (Fin.cons d (Fin.cons z Fin.elim0)) hc
    intro i
    exact Fin.cases hlook (Fin.cases
      (InternalRawListRecursionSupportProof.constantZero xs) (fun k => Fin.elim0 k)) i
  apply compositionValue InternalApplicationValidityStackAppend.append ![.projection 1,single]
    out xs (Fin.cons previous (Fin.cons singleton Fin.elim0)) ha
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases hsingle (fun k => Fin.elim0 k)) i

theorem singletonValue (Q : Program 2) (index previous input parameter d singleton : InternalGraphComposition.OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph3 (observation Q) d index input parameter)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton d z))) :
    Nonempty (Derivation body Delta
      (programGraph (.composition InternalListCodec.consCode
        ![.composition (observation Q) ![.projection 0,.projection 2,.projection 3],
          InternalAcceptance.constantZero 4]) singleton
        (Fin.cons index (Fin.cons previous (Fin.cons input (Fin.cons parameter Fin.elim0)))))) := by
  let xs : Fin 4 → InternalGraphComposition.OTerm alpha := Fin.cons index (Fin.cons previous (Fin.cons input (Fin.cons parameter Fin.elim0)))
  let look : Program 4 := .composition (observation Q) ![.projection 0,.projection 2,.projection 3]
  have hlook : Nonempty (Derivation body Delta (programGraph look d xs)) := by
    apply compositionValue (observation Q) ![.projection 0,.projection 2,.projection 3] d xs
      (Fin.cons index (Fin.cons input (Fin.cons parameter Fin.elim0))) hl
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs) (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k))) i
  apply compositionValue InternalListCodec.consCode ![look,InternalAcceptance.constantZero 4]
    singleton xs (Fin.cons d (Fin.cons z Fin.elim0)) hc
  intro i
  exact Fin.cases hlook (Fin.cases
    (InternalRawListRecursionSupportProof.constantZero xs) (fun k => Fin.elim0 k)) i

theorem scanAppendRecover (Q : Program 2) (index previous input parameter d singleton out : InternalGraphComposition.OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph3 (scan Q) previous index input parameter)))
    (ho : Nonempty (Derivation body Delta (graph3 (scan Q) out (suc index) input parameter)))
    (hl : Nonempty (Derivation body Delta (graph3 (observation Q) d index input parameter)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton d z))) :
    Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append out previous singleton)) := by
  have ht := recursionRecover (InternalAcceptance.constantZero 2) (step Q) out previous index
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hp ho
  let xs : Fin 4 → InternalGraphComposition.OTerm alpha := Fin.cons index (Fin.cons previous (Fin.cons input (Fin.cons parameter Fin.elim0)))
  let single : Program 4 := .composition InternalListCodec.consCode
    ![.composition (observation Q) ![.projection 0,.projection 2,.projection 3],
      InternalAcceptance.constantZero 4]
  apply compositionRecover InternalApplicationValidityStackAppend.append ![.projection 1,single]
    out xs (Fin.cons previous (Fin.cons singleton Fin.elim0)) ht
  intro i
  exact Fin.cases (projectionValue 1 xs)
    (Fin.cases (singletonValue Q index previous input parameter d singleton hl hc) (fun k => Fin.elim0 k)) i

theorem scanNext (Q : Program 2) (index previous input parameter d singleton out : InternalGraphComposition.OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph3 (scan Q) previous index input parameter)))
    (hl : Nonempty (Derivation body Delta (graph3 (observation Q) d index input parameter)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton d z)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append out previous singleton))) :
    Nonempty (Derivation body Delta (graph3 (scan Q) out (suc index) input parameter)) :=
  recursionNext (InternalAcceptance.constantZero 2) (step Q) out previous index
    (Fin.cons input (Fin.cons parameter Fin.elim0)) hp (stepValue Q index previous input parameter d singleton out hl hc ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsStepProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsStepProof
