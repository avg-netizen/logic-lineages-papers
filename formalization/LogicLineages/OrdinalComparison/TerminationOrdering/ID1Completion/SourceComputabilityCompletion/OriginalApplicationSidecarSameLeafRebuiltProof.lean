module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarEquationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafRebuiltProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z eqn sucRelabel zRelabel eqnRelabel)
open InternalTagArithmeticSupportProof (symm refl)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Fresh output payload witnesses reconstruct the actual raw parent before
using the paid sidecar application equation at this rebuilt input. -/
theorem sidecarAtPayloads (data : Data) (window : Program 1)
    (arrow d e f a rebuilt fp ap parameter : OrdinaryArithmetic.Term alpha)
    (har : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d a)))
    (hfr : Nonempty (Derivation body Delta (graph1 InternalUnpair.right fp f)))
    (haright : Nonempty (Derivation body Delta (graph1 InternalUnpair.right ap a)))
    (hr : Nonempty (Derivation body Delta (graph4 application rebuilt d e f a)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) rebuilt parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 (fold data window) f f parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (fold data window) a a parameter))) :
    Nonempty (Derivation body Delta (graph2 (fold data window) rebuilt rebuilt parameter)) := by
  have hc := andIntro har (andIntro (reconstructPair f arrow fp hfl hfr)
    (andIntro (reconstructPair a d ap hal haright)
      (InternalApplicationCertificateConstructorsSupportProof.applicationForward d e f a fp ap rebuilt hfr haright hr)))
  exact OriginalApplicationSidecarEquationSupportProof.applicationForward data window
    arrow d e fp ap f a rebuilt f a rebuilt parameter hc hv hf ha hr

/-- Bind both right fields of the rebuilt children internally, at the same
parameter. Original input payloads never stand for these output payloads. -/
theorem sidecarFixed (data : Data) (window : Program 1)
    (arrow d e f a rebuilt parameter : OrdinaryArithmetic.Term alpha)
    (har : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode arrow d e)))
    (hfl : Nonempty (Derivation body Delta (graph1 InternalUnpair.left arrow f)))
    (hal : Nonempty (Derivation body Delta (graph1 InternalUnpair.left d a)))
    (hr : Nonempty (Derivation body Delta (graph4 application rebuilt d e f a)))
    (hv : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (originalData data window)) (suc z) rebuilt parameter)))
    (hf : Nonempty (Derivation body Delta (graph2 (fold data window) f f parameter)))
    (ha : Nonempty (Derivation body Delta (graph2 (fold data window) a a parameter))) :
    Nonempty (Derivation body Delta (graph2 (fold data window) rebuilt rebuilt parameter)) := by
  let qs : Fin 2 → Program 2 := ![rightOf (.projection 0),rightOf (.projection 1)]
  let xs : Fin 2 → OrdinaryArithmetic.Term alpha := Fin.cons f (Fin.cons a Fin.elim0)
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph2Rename]
  have har' := renameInto har j Theta hj
  have hfl' := renameInto hfl j Theta hj
  have hal' := renameInto hal j Theta hj
  have hr' := renameInto hr j Theta hj
  have hv' := renameInto hv j Theta hj
  have hf' := renameInto hf j Theta hj
  have ha' := renameInto ha j Theta hj
  simp only [graph1Rename,graph2Rename,graph4Rename,sucRelabel,zRelabel] at har' hfl' hal' hr' hv' hf' ha'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 2 → OrdinaryArithmetic.Term beta := Fin.cons (f.relabel j) (Fin.cons (a.relabel j) Fin.elim0)
  have hfr := unaryRecover InternalUnpair.right (.projection 0) (ys 0) (f.relabel j)
    xx (hq 0) (projectionValue 0 xx)
  have haright := unaryRecover InternalUnpair.right (.projection 1) (ys 1) (a.relabel j)
    xx (hq 1) (projectionValue 1 xx)
  exact sidecarAtPayloads data window (arrow.relabel j) (d.relabel j) (e.relabel j)
    (f.relabel j) (a.relabel j) (rebuilt.relabel j) (ys 0) (ys 1) (parameter.relabel j)
    har' hfl' hal' hfr haright hr' hv' hf' ha'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafRebuiltProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSameLeafRebuiltProof
