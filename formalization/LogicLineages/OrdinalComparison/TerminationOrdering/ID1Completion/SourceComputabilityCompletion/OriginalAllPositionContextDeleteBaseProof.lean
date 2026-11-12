module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRawListRecursionSupportProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalTagArithmeticSyntaxProof
open InternalListCodecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalClassContextAllPositionObserver
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem frontZero (gamma : InternalGraphComposition.OTerm alpha) :
    Nonempty (Derivation body Delta (graph2 front z z gamma)) :=
  recursionZeroValue (InternalAcceptance.constantZero 1) frontStep z
    (Fin.cons gamma Fin.elim0) (InternalRawListRecursionSupportProof.constantZero _)

theorem dropOne (gamma d tail : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma d tail))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop tail (suc z) gamma)) :=
  dropNext tail gamma z gamma (dropZero gamma) (consTail gamma d tail hc)

theorem lookupZero (gamma d tail : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma d tail))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d z gamma)) :=
  lookupValue d z gamma gamma (dropZero gamma) (consHead gamma d tail hc)

theorem deleteValue (cutoff gamma frontValue suffix deleted : InternalGraphComposition.OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 front frontValue cutoff gamma)))
    (hd : Nonempty (Derivation body Delta
      (graph2 InternalRawListRecursion.drop suffix (suc cutoff) gamma)))
    (ha : Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append deleted frontValue suffix))) :
    Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma)) := by
  let xs : Fin 2 → InternalGraphComposition.OTerm alpha := Fin.cons cutoff (Fin.cons gamma Fin.elim0)
  let next : Program 2 := .composition .succ (fun _ : Fin 1 => .projection 0)
  let rest : Program 2 := .composition InternalRawListRecursion.drop ![next,.projection 1]
  have hn : Nonempty (Derivation body Delta (programGraph next (suc cutoff) xs)) := by
    apply compositionValue .succ (fun _ : Fin 1 => .projection 0) (suc cutoff) xs
      (Fin.cons cutoff Fin.elim0) (successorValue (Fin.cons cutoff Fin.elim0))
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have hr : Nonempty (Derivation body Delta (programGraph rest suffix xs)) := by
    apply compositionValue InternalRawListRecursion.drop ![next,.projection 1] suffix xs
      (Fin.cons (suc cutoff) (Fin.cons gamma Fin.elim0)) hd
    intro i
    exact Fin.cases hn (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k)) i
  apply compositionValue InternalApplicationValidityStackAppend.append ![front,rest] deleted xs
    (Fin.cons frontValue (Fin.cons suffix Fin.elim0)) ha
  intro i
  exact Fin.cases hf (Fin.cases hr (fun k => Fin.elim0 k)) i

theorem deleteAppendRecover (cutoff gamma frontValue suffix deleted : InternalGraphComposition.OTerm alpha)
    (hf : Nonempty (Derivation body Delta (graph2 front frontValue cutoff gamma)))
    (hd : Nonempty (Derivation body Delta
      (graph2 InternalRawListRecursion.drop suffix (suc cutoff) gamma)))
    (hv : Nonempty (Derivation body Delta (graph2 deleteAt deleted cutoff gamma))) :
    Nonempty (Derivation body Delta
      (graph2 InternalApplicationValidityStackAppend.append deleted frontValue suffix)) := by
  let xs : Fin 2 → InternalGraphComposition.OTerm alpha := Fin.cons cutoff (Fin.cons gamma Fin.elim0)
  let next : Program 2 := .composition .succ (fun _ : Fin 1 => .projection 0)
  let rest : Program 2 := .composition InternalRawListRecursion.drop ![next,.projection 1]
  have hn : Nonempty (Derivation body Delta (programGraph next (suc cutoff) xs)) := by
    apply compositionValue .succ (fun _ : Fin 1 => .projection 0) (suc cutoff) xs
      (Fin.cons cutoff Fin.elim0) (successorValue (Fin.cons cutoff Fin.elim0))
    intro i
    obtain rfl := Fin.eq_zero i
    exact projectionValue 0 xs
  have hr : Nonempty (Derivation body Delta (programGraph rest suffix xs)) := by
    apply compositionValue InternalRawListRecursion.drop ![next,.projection 1] suffix xs
      (Fin.cons (suc cutoff) (Fin.cons gamma Fin.elim0)) hd
    intro i
    exact Fin.cases hn (Fin.cases (projectionValue 1 xs) (fun k => Fin.elim0 k)) i
  apply compositionRecover InternalApplicationValidityStackAppend.append ![front,rest] deleted xs
    (Fin.cons frontValue (Fin.cons suffix Fin.elim0)) hv
  intro i
  exact Fin.cases hf (Fin.cases hr (fun k => Fin.elim0 k)) i

theorem deleteZero (gamma d tail : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma d tail))) :
    Nonempty (Derivation body Delta (graph2 deleteAt tail z gamma)) :=
  deleteValue z gamma z tail tail (frontZero gamma) (dropOne gamma d tail hc)
    (InternalApplicationValidityStackAppendListProof.appendZeroValue tail)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteBaseProof
