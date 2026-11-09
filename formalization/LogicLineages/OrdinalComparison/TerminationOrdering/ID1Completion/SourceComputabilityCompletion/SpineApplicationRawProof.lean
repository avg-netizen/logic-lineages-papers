module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationRawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeelSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalControlGraphSupportProof (emptyRename)
open InternalTagArithmeticSyntaxProof (OTerm)
open InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def queries : Fin 3 → Program 2 :=
  Fin.cons (rightOf (.projection 0)) (Fin.cons (rightOf (.projection 1))
    (Fin.cons (.composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 1)) Fin.elim0))

theorem query0 : queries (0 : Fin 3) = rightOf (.projection (0 : Fin 2)) := rfl
theorem query1 : queries (1 : Fin 3) = rightOf (.projection (1 : Fin 2)) := rfl
theorem query2 : queries (2 : Fin 3) =
    .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection (1 : Fin 2)) := rfl

theorem equationRename {β : Type} (mark parent flag next : OTerm α) (j : α → β) :
    ((BottomSpineMeasure.graph mark parent).iff (graph2 InternalPairing.pairing mark flag next)).relabel j =
      (BottomSpineMeasure.graph (mark.relabel j) (parent.relabel j)).iff
        (graph2 InternalPairing.pairing (mark.relabel j) (flag.relabel j) (next.relabel j)) := by
  change ((graph1 BottomSpineMeasure.measure mark parent).relabel j).iff
    ((graph2 InternalPairing.pairing mark flag next).relabel j) = _
  rw [graph1Rename,graph2Rename]
  rfl

theorem atPayloads (arrow d e f a parent fm flag depth next mark fp ap am : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hr : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hfm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm f)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flag fm)))
    (hd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right depth fm)))
    (hs : Nonempty (Derivation body Gamma (graph1 Program.succ next depth)))
    (hfr : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (haright : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right ap a)))
    (ham : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph am a))) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark parent).iff (graph2 InternalPairing.pairing mark flag next))) := by
  have hp := applicationForward d e f a fp ap parent hfr haright hr
  have hc := andIntro har (andIntro (reconstructPair f arrow fp hfl hfr)
    (andIntro (reconstructPair a d ap hal haright) hp))
  have H := andIntro hc (andIntro hfm (andIntro ham (andIntro hl (andIntro hd hs))))
  let P := BottomSpineMeasure.graph mark parent
  let Q := graph2 InternalPairing.pairing mark flag next
  obtain ⟨hh⟩ := H
  obtain ⟨hf⟩ := BottomSpineMeasureInternalProof.forward arrow d e fp ap f a parent fm am flag depth next mark
    ⟨addHyp hh P⟩ (show Nonempty (Derivation body (P :: Gamma) P) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := BottomSpineMeasureInternalProof.backward arrow d e fp ap f a parent fm am flag depth next mark
    ⟨addHyp hh Q⟩ (show Nonempty (Derivation body (Q :: Gamma) Q) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

/-- The argument's measure is supplied by original Program totality and
then discarded. Only the function's mark appears in the conclusion. -/
theorem rawEquation (arrow d e f a parent fm flag depth next mark : OTerm α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d a)))
    (hr : Nonempty (Derivation body Gamma (graph4 application parent d e f a)))
    (hfm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm f)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flag fm)))
    (hd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right depth fm)))
    (hs : Nonempty (Derivation body Gamma (graph1 Program.succ next depth))) :
    Nonempty (Derivation body Gamma
      ((BottomSpineMeasure.graph mark parent).iff (graph2 InternalPairing.pairing mark flag next))) := by
  let xs : Fin 2 → OTerm α := Fin.cons f (Fin.cons a Fin.elim0)
  apply queryCases queries xs _
  intro β j ys Delta hj hq
  rw [equationRename]
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OTerm β := Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)
  have hq0 := hq 0
  rw [query0] at hq0
  have hq1 := hq 1
  rw [query1] at hq1
  have hq2 := hq 2
  rw [query2] at hq2
  have hfr := unaryRecover InternalUnpair.right (.projection (0 : Fin 2)) (ys 0)
    (f.relabel j) xx hq0 (projectionValue 0 xx)
  have haright := unaryRecover InternalUnpair.right (.projection (1 : Fin 2)) (ys 1)
    (a.relabel j) xx hq1 (projectionValue 1 xx)
  have ham := unaryRecover BottomSpineMeasure.measure (.projection (1 : Fin 2)) (ys 2)
    (a.relabel j) xx hq2 (projectionValue 1 xx)
  have har' := renameInto har j Delta hj
  rw [graph2Rename] at har'
  have hfl' := renameInto hfl j Delta hj
  rw [graph1Rename] at hfl'
  have hal' := renameInto hal j Delta hj
  rw [graph1Rename] at hal'
  have hr' := renameInto hr j Delta hj
  rw [graph4Rename] at hr'
  have hfm' := renameInto hfm j Delta hj
  simp only [BottomSpineMeasure.graph,graph1Rename] at hfm'
  have hl' := renameInto hl j Delta hj
  rw [graph1Rename] at hl'
  have hd' := renameInto hd j Delta hj
  rw [graph1Rename] at hd'
  have hs' := renameInto hs j Delta hj
  rw [graph1Rename] at hs'
  exact atPayloads (arrow.relabel j) (d.relabel j) (e.relabel j) (f.relabel j) (a.relabel j)
    (parent.relabel j) (fm.relabel j) (flag.relabel j) (depth.relabel j) (next.relabel j) (mark.relabel j)
    (ys 0) (ys 1) (ys 2) har' hfl' hal' hr' hfm' hl' hd' hs' hfr haright ham

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationRawProof
