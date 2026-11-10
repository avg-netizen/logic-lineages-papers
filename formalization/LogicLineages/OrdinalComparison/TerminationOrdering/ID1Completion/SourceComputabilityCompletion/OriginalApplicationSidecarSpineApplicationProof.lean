module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationRawProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open OriginalApplicationSidecarSpine OriginalApplicationSidecarSpineSyntaxProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro queryCases)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Both actual raw applications have the same function mark. Their exact
raw spine equations identify every parent mark with the same pairing graph. -/
theorem atCoordinates
    (arrow d e fn arg functionOut argumentOut input out fm flag depth next value : OrdinaryArithmetic.Term α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow fn)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d arg)))
    (hfol : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow functionOut)))
    (haol : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d argumentOut)))
    (hi : Nonempty (Derivation body Gamma (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Gamma (graph4 application out d e functionOut argumentOut)))
    (hfm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm fn)))
    (hfo : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm functionOut)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left flag fm)))
    (hd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right depth fm)))
    (hs : Nonempty (Derivation body Gamma (graph1 Program.succ next depth))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  obtain ⟨original⟩ := SpineApplicationRawProof.rawEquation arrow d e fn arg input fm flag depth next value
    har hfl hal hi hfm hl hd hs
  obtain ⟨rebuilt⟩ := SpineApplicationRawProof.rawEquation arrow d e functionOut argumentOut out fm flag depth next value
    har hfol haol ho hfo hl hd hs
  let A := BottomSpineMeasure.graph value out
  let B := BottomSpineMeasure.graph value input
  have forward : Derivation body (A :: Gamma) B :=
    Derivation.implicationElimination (addHyp (Derivation.conjunctionRight original) A)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft rebuilt) A)
        (Derivation.hypothesis List.mem_cons_self))
  have backward : Derivation body (B :: Gamma) A :=
    Derivation.implicationElimination (addHyp (Derivation.conjunctionRight rebuilt) B)
      (Derivation.implicationElimination (addHyp (Derivation.conjunctionLeft original) B)
        (Derivation.hypothesis List.mem_cons_self))
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

/-- Query actual mark coordinates and successor internally. The raw equation
itself binds fresh original/rebuilt child payloads and argument measures. -/
theorem atFunctionMark
    (arrow d e fn arg functionOut argumentOut input out fm value : OrdinaryArithmetic.Term α)
    (har : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow fn)))
    (hal : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d arg)))
    (hfol : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left arrow functionOut)))
    (haol : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left d argumentOut)))
    (hi : Nonempty (Derivation body Gamma (graph4 application input d e fn arg)))
    (ho : Nonempty (Derivation body Gamma (graph4 application out d e functionOut argumentOut)))
    (hfm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm fn)))
    (hfo : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph fm functionOut))) :
    Nonempty (Derivation body Gamma (conclusion out input value)) := by
  let qs : Fin 3 → Program 1 := Fin.cons (leftOf (.projection 0))
    (Fin.cons (rightOf (.projection 0))
      (Fin.cons (.composition Program.succ (fun _ : Fin 1 => rightOf (.projection 0))) Fin.elim0))
  let xs : Fin 1 → OrdinaryArithmetic.Term α := Fin.cons fm Fin.elim0
  apply queryCases qs xs _
  intro β j ys Delta hj hq
  rw [conclusionRename]
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 1 → OrdinaryArithmetic.Term β := Fin.cons (fm.relabel j) Fin.elim0
  have hl := unaryRecover InternalUnpair.left (.projection (0 : Fin 1)) (ys 0)
    (fm.relabel j) xx (hq 0) (projectionValue 0 xx)
  have hd := unaryRecover InternalUnpair.right (.projection (0 : Fin 1)) (ys 1)
    (fm.relabel j) xx (hq 1) (projectionValue 0 xx)
  have hs := unaryRecover Program.succ (rightOf (.projection (0 : Fin 1))) (ys 2)
    (ys 1) xx (hq 2) (hq 1)
  have har' := renameInto har j Delta hj
  rw [graph2Rename] at har'
  have hfl' := renameInto hfl j Delta hj
  have hal' := renameInto hal j Delta hj
  have hfol' := renameInto hfol j Delta hj
  have haol' := renameInto haol j Delta hj
  rw [graph1Rename] at hfl' hal' hfol' haol'
  have hi' := renameInto hi j Delta hj
  have ho' := renameInto ho j Delta hj
  rw [graph4Rename] at hi' ho'
  have hfm' := renameInto hfm j Delta hj
  have hfo' := renameInto hfo j Delta hj
  simp only [BottomSpineMeasure.graph,graph1Rename] at hfm' hfo'
  exact atCoordinates (arrow.relabel j) (d.relabel j) (e.relabel j)
    (fn.relabel j) (arg.relabel j) (functionOut.relabel j) (argumentOut.relabel j)
    (input.relabel j) (out.relabel j) (fm.relabel j) (ys 0) (ys 1) (ys 2) (value.relabel j)
    har' hfl' hal' hfol' haol' hi' ho' hfm' hfo' hl hd hs

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineApplicationProof
