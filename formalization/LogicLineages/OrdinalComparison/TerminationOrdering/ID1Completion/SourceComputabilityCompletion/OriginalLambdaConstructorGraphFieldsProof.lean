module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open OriginalLambdaConstructor OriginalLambdaConstructorGraphSyntaxProof OriginalLambdaConstructorGraphSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- The body's outer type is retained, not silently replaced by the supplied
codomain. Internal unpair inversion reassembles the very same packed body. -/
theorem constructorFields (out d e b arrowCode : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph3 constructor out d e b)))
    (hb : Nonempty (Derivation body Delta (graph1 InternalUnpair.left e b)))
    (ha : Nonempty (Derivation body Delta (graph2 arrow arrowCode d e))) :
    Nonempty (Derivation body Delta (Fields out d e b arrowCode)) := by
  let payload : Program 3 := rightOf (.projection 2)
  let inner : Program 3 := pairOf (.projection 0) payload
  let node : Program 3 := pairOf (InternalLessThan.constantOne 3) inner
  let qs : Fin 3 → Program 3 := ![payload,inner,node]
  let xs : Fin 3 → OTerm alpha := Fin.cons d (Fin.cons e (Fin.cons b Fin.elim0))
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [fieldsRename]
  have hc' := renameInto hc j Theta hj
  have hb' := renameInto hb j Theta hj
  have ha' := renameInto ha j Theta hj
  rw [graph3Rename] at hc'
  rw [graph1Rename] at hb'
  rw [graph2Rename] at ha'
  simp only [xs,consTermRename,emptyRename] at hq
  let xx : Fin 3 → OTerm beta := Fin.cons (d.relabel j)
    (Fin.cons (e.relabel j) (Fin.cons (b.relabel j) Fin.elim0))
  have hp := unaryRecover InternalUnpair.right (.projection 2) (ys 0) (b.relabel j) xx
    (hq 0) (projectionValue 2 xx)
  have hi := binaryRecover InternalPairing.pairing (.projection 0) payload
    (ys 1) (d.relabel j) (ys 0) xx (hq 1) (projectionValue 0 xx) (hq 0)
  have hn := binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 3) inner
    (ys 2) (numeral 1) (ys 1) xx (hq 2)
    (InternalLessThanSupportProof.oneConstantValue xx) (hq 1)
  have hpacked := constructorForward (out.relabel j) (d.relabel j) (e.relabel j)
    (b.relabel j) (ys 0) hp hc'
  have ho := packedOuter (out.relabel j) (d.relabel j) (e.relabel j) (ys 0)
    (arrowCode.relabel j) (ys 1) (ys 2) ha' hi hn hpacked
  have hfields := selectorsAtPairs (out.relabel j) (d.relabel j) (ys 0)
    (arrowCode.relabel j) (ys 1) (ys 2) hi hn ho
  have hbody := bodyCodeValue (b.relabel j) (e.relabel j) (out.relabel j) (ys 0)
    (reconstructPair (b.relabel j) (e.relabel j) (ys 0) hb' hp)
    (andRight (andRight (andRight hfields)))
  exact andIntro (andLeft hfields) (andIntro (andLeft (andRight hfields))
    (andIntro ha' (andIntro (andLeft (andRight (andRight hfields))) hbody)))

theorem actualOriginalLambdaConstructorFields :
    OriginalLambdaConstructorTargets.ActualOriginalLambdaConstructorFields := by
  intro body alpha Delta out d e b arrowCode
  let A := graph3 constructor out d e b ⊓
    (graph1 InternalUnpair.left e b ⊓ graph2 arrow arrowCode d e)
  have h : Nonempty (Derivation body (A :: Delta) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := constructorFields out d e b arrowCode
    (andLeft h) (andLeft (andRight h)) (andRight (andRight h))
  exact ⟨Derivation.implicationIntroduction hf⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphFieldsProof
