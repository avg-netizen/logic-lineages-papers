module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedCollectionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixSpineCompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc)
open InternalOriginalOrderSyntaxProof (ltF)
open PositiveSpineRulesProof
open UniformCertificateCompletion.PositiveGuard
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Compose the actual conditional flag/depth consequences, without assuming
that any source is a bottom spine. Intermediate flaggedness is derived by
applying the first implication, then used in the second implication. -/
theorem flaggedTrans (sm vm tm sd vd td : OTerm alpha)
    (hfirst : Nonempty (Derivation body Gamma
      ((graph1 InternalUnpair.left (suc z) sm).imp
        (graph1 InternalUnpair.left (suc z) vm ⊓ ltF vd sd))))
    (hsecond : Nonempty (Derivation body Gamma
      ((graph1 InternalUnpair.left (suc z) vm).imp
        (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td vd)))) :
    Nonempty (Derivation body Gamma
      ((graph1 InternalUnpair.left (suc z) sm).imp
        (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td sd))) := by
  let P := graph1 InternalUnpair.left (suc z) sm
  obtain ⟨hfirst'⟩ := withHyp hfirst P
  have hv : Nonempty (Derivation body (P :: Gamma)
      (graph1 InternalUnpair.left (suc z) vm ⊓ ltF vd sd)) :=
    ⟨Derivation.implicationElimination hfirst' (Derivation.hypothesis List.mem_cons_self)⟩
  obtain ⟨hsecond'⟩ := withHyp hsecond P
  obtain ⟨hvflag⟩ := andLeft hv
  have ht : Nonempty (Derivation body (P :: Gamma)
      (graph1 InternalUnpair.left (suc z) tm ⊓ ltF td vd)) :=
    ⟨Derivation.implicationElimination hsecond' hvflag⟩
  have hlt := InternalBoundedCollectionSupportProof.ltTrans td vd sd (andRight ht) (andRight hv)
  obtain ⟨hout⟩ := andIntro (andLeft ht) hlt
  exact ⟨Derivation.implicationIntroduction hout⟩

/-- The certificate coordinates are kept explicit and may differ: the guard
reads only its raw endpoints. This lemma composes literal Program guards
using their actual mark graphs, rather than replacing them by a new relation. -/
theorem spineTransAtMarks (measure : Program 1)
    (x vertex y first second code parameter sm vm tm sd vd td : OTerm alpha)
    (hsm : Nonempty (Derivation body Gamma (graph1 measure sm x)))
    (hvm : Nonempty (Derivation body Gamma (graph1 measure vm vertex)))
    (htm : Nonempty (Derivation body Gamma (graph1 measure tm y)))
    (hsd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right sd sm)))
    (hvd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right vd vm)))
    (htd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right td tm)))
    (hfirst : Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) x vertex first parameter)))
    (hsecond : Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) vertex y second parameter))) :
    Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) x y code parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons x (Fin.cons vertex (Fin.cons first (Fin.cons parameter Fin.elim0)))
  let vs : Fin 4 → OTerm alpha := Fin.cons vertex (Fin.cons y (Fin.cons second (Fin.cons parameter Fin.elim0)))
  let ys : Fin 4 → OTerm alpha := Fin.cons x (Fin.cons y (Fin.cons code (Fin.cons parameter Fin.elim0)))
  have hf := spineRecover measure sm vm sd vd xs hsm hvm hsd hvd hfirst
  have ht := spineRecover measure vm tm vd td vs hvm htm hvd htd hsecond
  exact spineValue measure sm tm sd td ys hsm htm hsd htd (flaggedTrans sm vm tm sd vd td hf ht)

/-- Bind all three original marks and depths internally by Program totality.
The final guard keeps the requested path code, not either edge certificate. -/
theorem spineTrans (measure : Program 1)
    (x vertex y first second code parameter : OTerm alpha)
    (hfirst : Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) x vertex first parameter)))
    (hsecond : Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) vertex y second parameter))) :
    Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) x y code parameter)) := by
  let m0 : Program 3 := .composition measure (fun _ : Fin 1 => .projection 0)
  let m1 : Program 3 := .composition measure (fun _ : Fin 1 => .projection 1)
  let m2 : Program 3 := .composition measure (fun _ : Fin 1 => .projection 2)
  let qs : Fin 6 → Program 3 := Fin.cons m0 (Fin.cons m1 (Fin.cons m2 (Fin.cons (rightOf m0) (Fin.cons (rightOf m1) (Fin.cons (rightOf m2) Fin.elim0)))))
  let xs : Fin 3 → OTerm alpha := Fin.cons x (Fin.cons vertex (Fin.cons y Fin.elim0))
  apply queryCases qs xs _
  intro beta j ms Delta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  simp only [graph4Rename,sucRelabel,zRelabel]
  let ys : Fin 3 → OTerm beta := Fin.cons (x.relabel j) (Fin.cons (vertex.relabel j) (Fin.cons (y.relabel j) Fin.elim0))
  have hm0 : Nonempty (Derivation body Delta (programGraph m0 (ms 0) ys)) := by
    have hv := hq 0
    rw [show qs (0 : Fin 6) = m0 from rfl] at hv
    exact hv
  have hm1 : Nonempty (Derivation body Delta (programGraph m1 (ms 1) ys)) := by
    have hv := hq 1
    rw [show qs (1 : Fin 6) = m1 from rfl] at hv
    exact hv
  have hm2 : Nonempty (Derivation body Delta (programGraph m2 (ms 2) ys)) := by
    have hv := hq 2
    rw [show qs (2 : Fin 6) = m2 from rfl] at hv
    exact hv
  have hsm := unaryRecover measure (.projection (0 : Fin 3)) (ms 0) (x.relabel j) ys hm0 (projectionValue 0 ys)
  have hvm := unaryRecover measure (.projection (1 : Fin 3)) (ms 1) (vertex.relabel j) ys hm1 (projectionValue 1 ys)
  have htm := unaryRecover measure (.projection (2 : Fin 3)) (ms 2) (y.relabel j) ys hm2 (projectionValue 2 ys)
  have hd0 : Nonempty (Derivation body Delta (programGraph (rightOf m0) (ms 3) ys)) := by
    have hv := hq 3
    rw [show qs (3 : Fin 6) = (rightOf m0) from rfl] at hv
    exact hv
  have hd1 : Nonempty (Derivation body Delta (programGraph (rightOf m1) (ms 4) ys)) := by
    have hv := hq 4
    rw [show qs (4 : Fin 6) = (rightOf m1) from rfl] at hv
    exact hv
  have hd2 : Nonempty (Derivation body Delta (programGraph (rightOf m2) (ms 5) ys)) := by
    have hv := hq 5
    rw [show qs (5 : Fin 6) = (rightOf m2) from rfl] at hv
    exact hv
  have hsd := unaryRecover InternalUnpair.right m0 (ms 3) (ms 0) ys hd0 hm0
  have hvd := unaryRecover InternalUnpair.right m1 (ms 4) (ms 1) ys hd1 hm1
  have htd := unaryRecover InternalUnpair.right m2 (ms 5) (ms 2) ys hd2 hm2
  have hf := renameInto hfirst j Delta hj
  have ht := renameInto hsecond j Delta hj
  simp only [graph4Rename,sucRelabel,zRelabel] at hf ht
  exact spineTransAtMarks measure (x.relabel j) (vertex.relabel j) (y.relabel j)
    (first.relabel j) (second.relabel j) (code.relabel j) (parameter.relabel j)
    (ms 0) (ms 1) (ms 2) (ms 3) (ms 4) (ms 5) hsm hvm htm hsd hvd htd hf ht

/-- Only the endpoints are read by the original guard. Bind their marks and
depths internally before changing a certificate coordinate. -/
theorem spineRecode (measure : Program 1) (x y oldCode code parameter : OTerm alpha)
    (h : Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) x y oldCode parameter))) :
    Nonempty (Derivation body Gamma
      (graph4 (spineGuard measure) (suc z) x y code parameter)) := by
  let m0 : Program 2 := .composition measure (fun _ : Fin 1 => .projection 0)
  let m1 : Program 2 := .composition measure (fun _ : Fin 1 => .projection 1)
  let qs : Fin 4 → Program 2 := Fin.cons m0 (Fin.cons m1 (Fin.cons (rightOf m0) (Fin.cons (rightOf m1) Fin.elim0)))
  let xs : Fin 2 → OTerm alpha := Fin.cons x (Fin.cons y Fin.elim0)
  apply queryCases qs xs _
  intro beta j ms Delta hj hq
  simp only [xs,consTermRename,emptyRename] at hq
  simp only [graph4Rename,sucRelabel,zRelabel]
  let ys : Fin 2 → OTerm beta := Fin.cons (x.relabel j) (Fin.cons (y.relabel j) Fin.elim0)
  have hm0 : Nonempty (Derivation body Delta (programGraph m0 (ms 0) ys)) := by
    have hv := hq 0
    rw [show qs (0 : Fin 4) = m0 from rfl] at hv
    exact hv
  have hm1 : Nonempty (Derivation body Delta (programGraph m1 (ms 1) ys)) := by
    have hv := hq 1
    rw [show qs (1 : Fin 4) = m1 from rfl] at hv
    exact hv
  have hd0 : Nonempty (Derivation body Delta (programGraph (rightOf m0) (ms 2) ys)) := by
    have hv := hq 2
    rw [show qs (2 : Fin 4) = (rightOf m0) from rfl] at hv
    exact hv
  have hd1 : Nonempty (Derivation body Delta (programGraph (rightOf m1) (ms 3) ys)) := by
    have hv := hq 3
    rw [show qs (3 : Fin 4) = (rightOf m1) from rfl] at hv
    exact hv
  have hsm := unaryRecover measure (.projection (0 : Fin 2)) (ms 0) (x.relabel j) ys hm0 (projectionValue 0 ys)
  have htm := unaryRecover measure (.projection (1 : Fin 2)) (ms 1) (y.relabel j) ys hm1 (projectionValue 1 ys)
  have hsd := unaryRecover InternalUnpair.right m0 (ms 2) (ms 0) ys hd0 hm0
  have htd := unaryRecover InternalUnpair.right m1 (ms 3) (ms 1) ys hd1 hm1
  have h' := renameInto h j Delta hj
  simp only [graph4Rename,sucRelabel,zRelabel] at h'
  let old : Fin 4 → OTerm beta := Fin.cons (x.relabel j) (Fin.cons (y.relabel j) (Fin.cons (oldCode.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
  let fresh : Fin 4 → OTerm beta := Fin.cons (x.relabel j) (Fin.cons (y.relabel j) (Fin.cons (code.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
  exact spineValue measure (ms 0) (ms 1) (ms 2) (ms 3) fresh hsm htm hsd htd
    (spineRecover measure (ms 0) (ms 1) (ms 2) (ms 3) old hsm htm hsd htd h')

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixSpineCompositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSameCodeSuffixSpineCompositionProof
