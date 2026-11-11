module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineMarkProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineRawProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (unaryRecover)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion UniformCertificateCompletion.SupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

def queries : Fin 6 → Program 4 :=
  let leftS : Program 4 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 0)
  let leftT : Program 4 := .composition InternalUnpair.left (fun _ : Fin 1 => .projection 1)
  let markX : Program 4 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 2)
  let markY : Program 4 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 3)
  let depthX : Program 4 := .composition InternalUnpair.right (fun _ : Fin 1 => markX)
  let depthY : Program 4 := .composition InternalUnpair.right (fun _ : Fin 1 => markY)
  Fin.cons leftS (Fin.cons leftT (Fin.cons markX
    (Fin.cons markY (Fin.cons depthX (Fin.cons depthY Fin.elim0)))))

theorem spineRename {beta : Type} (x y certificate parameter : OTerm alpha) (j : alpha → beta) :
    (OriginalSpineGuardLeaf.spineAccepted x y certificate parameter).relabel j =
      OriginalSpineGuardLeaf.spineAccepted (x.relabel j) (y.relabel j)
        (certificate.relabel j) (parameter.relabel j) := by
  simp only [OriginalSpineGuardLeaf.spineAccepted,graph4Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

/-- Source tags, whole endpoint marks and their depths are actual Program
outputs, eliminated internally by the original arithmetic totality rule. -/
theorem atRaw (data : Data) (window : Program 1) (oldStep : Program 4)
    (hFold : OriginalFullFoldSpine.FullFoldMarkPreservation data window)
    (hStep : OriginalSelectedStepSpine.RawStepHasSpineGuard data oldStep)
    (x y certificate S T K parameter : OTerm alpha)
    (hw : Nonempty (Derivation body Gamma
      (OriginalFunctionNeutrality.windowGraph window x parameter)))
    (hr : Nonempty (Derivation body Gamma (requirements data oldStep x y S T K parameter))) :
    Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted x y certificate parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons S (Fin.cons T (Fin.cons x (Fin.cons y Fin.elim0)))
  apply queryCases queries xs _
  intro beta j ys Delta hj hq
  rw [spineRename]
  let zs : Fin 4 → OTerm beta := fun i => (xs i).relabel j
  have hw' := renameInto hw j Delta hj
  simp only [OriginalFunctionNeutrality.windowGraph,OriginalVariableRepresentative.windowGraph,
    graph2Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel] at hw'
  have hr' := renameInto hr j Delta hj
  rw [requirementsRename] at hr'
  have hs : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.left (ys 0) (S.relabel j))) :=
    unaryRecover InternalUnpair.left (.projection 0) (ys 0) (S.relabel j) zs (hq 0)
      (projectionValue 0 zs)
  have ht : Nonempty (Derivation body Delta
      (graph1 InternalUnpair.left (ys 1) (T.relabel j))) :=
    unaryRecover InternalUnpair.left (.projection 1) (ys 1) (T.relabel j) zs (hq 1)
      (projectionValue 1 zs)
  have hmX : Nonempty (Derivation body Delta
      (BottomSpineMeasure.graph (ys 2) (x.relabel j))) :=
    unaryRecover BottomSpineMeasure.measure (.projection 2) (ys 2) (x.relabel j) zs (hq 2)
      (projectionValue 2 zs)
  have hmY : Nonempty (Derivation body Delta
      (BottomSpineMeasure.graph (ys 3) (y.relabel j))) :=
    unaryRecover BottomSpineMeasure.measure (.projection 3) (ys 3) (y.relabel j) zs (hq 3)
      (projectionValue 3 zs)
  have hdX : Nonempty (Derivation body Delta (graph1 InternalUnpair.right (ys 4) (ys 2))) :=
    unaryRecover InternalUnpair.right (queries 2) (ys 4) (ys 2) zs (hq 4) (hq 2)
  have hdY : Nonempty (Derivation body Delta (graph1 InternalUnpair.right (ys 5) (ys 3))) :=
    unaryRecover InternalUnpair.right (queries 3) (ys 5) (ys 3) zs (hq 5) (hq 3)
  exact OriginalQuotientSpineMarkProof.atMarks data window oldStep hFold hStep
    (x.relabel j) (y.relabel j) (certificate.relabel j) (S.relabel j) (T.relabel j)
    (K.relabel j) (parameter.relabel j) (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) (ys 5)
    hw' hr' hs ht hmX hmY hdX hdY

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineRawProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineRawProof
