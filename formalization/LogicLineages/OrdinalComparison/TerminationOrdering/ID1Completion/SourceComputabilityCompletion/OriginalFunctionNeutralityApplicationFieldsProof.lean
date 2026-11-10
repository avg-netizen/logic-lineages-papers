module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationStepPeel
open InternalApplicationStepPeelSupportProof InternalApplicationStepPeelComponentsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Recover the function payload from the unchanged original packed
application constructor, without interpreting any child as a typed term. -/
theorem packedFunctionPayload (d e fp ap parent : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 packedApplication parent d e fp ap))) :
    Nonempty (Derivation body Delta
      (graph1 (functionPayload (.projection 0)) fp parent)) := by
  let children : Program 4 := pairOf (.projection 2) (.projection 3)
  let middle : Program 4 := pairOf (.projection 0) children
  let node : Program 4 := pairOf (two 4) middle
  let qs : Fin 3 → Program 4 := ![children,middle,node]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fp (Fin.cons ap Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have hp' := renameInto hp j Theta hj
  rw [graph4Rename] at hp'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fp.relabel j) (Fin.cons (ap.relabel j) Fin.elim0)))
  have hc := binaryRecover InternalPairing.pairing (.projection 2) (.projection 3)
    (ys 0) (fp.relabel j) (ap.relabel j) xx (hq 0) (projectionValue 2 xx) (projectionValue 3 xx)
  have hm := binaryRecover InternalPairing.pairing (.projection 0) children
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (two 4) middle
    (ys 2) positionTerm (ys 1) xx (hq 2) (twoValue xx) (hq 1)
  have hpar := binaryRecover InternalPairing.pairing (.projection 1) node
    (parent.relabel j) (e.relabel j) (ys 2) xx hp' (projectionValue 1 xx) (hq 2)
  let ss : Fin 1 → OTerm beta := Fin.cons (parent.relabel j) Fin.elim0
  have fields := fieldsAtPairs (.projection 0) (parent.relabel j) (parent.relabel j)
    (d.relabel j) (e.relabel j) (fp.relabel j) (ap.relabel j) (ys 0) (ys 1) (ys 2)
    (projectionValue 0 ss) hc hm hn hpar
  exact andLeft (andRight (andRight (andRight fields)))

/-- A raw application's function-payload tag is the actual tag of its
supplied whole function. Only original pair projections are used. -/
theorem rawFunctionTag (d e fn arg parent tag : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph4 application parent d e fn arg)))
    (ht : Nonempty (Derivation body Delta (OriginalConstructorShape.tagGraph tag fn))) :
    Nonempty (Derivation body Delta
      (graph1 (leftOf (functionPayload (.projection 0))) tag parent)) := by
  let qs : Fin 2 → Program 4 := ![rightOf (.projection 2),rightOf (.projection 3)]
  let xs : Fin 4 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons fn (Fin.cons arg Fin.elim0)))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  have hp' := renameInto hp j Theta hj
  rw [graph4Rename] at hp'
  have ht' := renameInto ht j Theta hj
  rw [graph1Rename] at ht'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 4 → OTerm beta := Fin.cons (d.relabel j) (Fin.cons (e.relabel j)
    (Fin.cons (fn.relabel j) (Fin.cons (arg.relabel j) Fin.elim0)))
  have hf := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (fn.relabel j) xx
    (hq 0) (projectionValue 2 xx)
  have ha := unaryRecover InternalUnpair.right (.projection 3) (ys 1) (arg.relabel j) xx
    (hq 1) (projectionValue 3 xx)
  have hpacked := applicationForward (d.relabel j) (e.relabel j) (fn.relabel j)
    (arg.relabel j) (ys 0) (ys 1) (parent.relabel j) hf ha hp'
  have hpayload := packedFunctionPayload (d.relabel j) (e.relabel j)
    (ys 0) (ys 1) (parent.relabel j) hpacked
  let ff : Fin 1 → OTerm beta := Fin.cons (fn.relabel j) Fin.elim0
  have hright := unaryValue InternalUnpair.right (.projection 0) (ys 0) (fn.relabel j)
    ff hf (projectionValue 0 ff)
  have htag := unaryRecover InternalUnpair.left (rightOf (.projection 0))
    (tag.relabel j) (ys 0) ff ht' hright
  exact unaryValue InternalUnpair.left (functionPayload (.projection 0))
    (tag.relabel j) (ys 0) (Fin.cons (parent.relabel j) Fin.elim0) htag hpayload

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionNeutralityApplicationFieldsProof
