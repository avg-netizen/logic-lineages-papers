module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontStepProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRawListRecursionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSyntaxProof
open InternalListCodecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem stepValue (index previous gamma d singleton out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d index gamma)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton d z)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append out previous singleton))) :
    Nonempty (Derivation body Delta
      (programGraph frontStep out (Fin.cons index (Fin.cons previous (Fin.cons gamma Fin.elim0))))) := by
  let xs : Fin 3 → OTerm alpha := Fin.cons index (Fin.cons previous (Fin.cons gamma Fin.elim0))
  let look : Program 3 := .composition InternalRawListRecursion.lookup ![.projection 0,.projection 2]
  let single : Program 3 := .composition InternalListCodec.consCode
    ![look,InternalAcceptance.constantZero 3]
  have hlook : Nonempty (Derivation body Delta (programGraph look d xs)) := by
    apply compositionValue InternalRawListRecursion.lookup ![.projection 0,.projection 2] d xs
      (Fin.cons index (Fin.cons gamma Fin.elim0)) hl
    intro i
    exact Fin.cases (projectionValue 0 xs)
      (Fin.cases (projectionValue 2 xs) (fun k => Fin.elim0 k)) i
  have hsingle : Nonempty (Derivation body Delta (programGraph single singleton xs)) := by
    apply compositionValue InternalListCodec.consCode ![look,InternalAcceptance.constantZero 3]
      singleton xs (Fin.cons d (Fin.cons z Fin.elim0)) hc
    intro i
    exact Fin.cases hlook (Fin.cases
      (InternalRawListRecursionSupportProof.constantZero xs) (fun k => Fin.elim0 k)) i
  apply compositionValue InternalApplicationValidityStackAppend.append ![.projection 1,single]
    out xs (Fin.cons previous (Fin.cons singleton Fin.elim0)) ha
  intro i
  exact Fin.cases (projectionValue 1 xs) (Fin.cases hsingle (fun k => Fin.elim0 k)) i

theorem frontNext (index previous gamma d singleton out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 front previous index gamma)))
    (hl : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d index gamma)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton d z)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append out previous singleton))) :
    Nonempty (Derivation body Delta (graph2 front out (suc index) gamma)) :=
  recursionNext (InternalAcceptance.constantZero 1) frontStep out previous index
    (Fin.cons gamma Fin.elim0) hp (stepValue index previous gamma d singleton out hl hc ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontStepProof
