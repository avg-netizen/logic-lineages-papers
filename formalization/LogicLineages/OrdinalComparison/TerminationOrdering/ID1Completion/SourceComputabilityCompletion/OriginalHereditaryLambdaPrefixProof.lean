module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalHereditaryLambda OriginalHereditaryLambdaPrefixSupportProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Every required original selector witness is supplied by internal Program
totality. The path, its literal tail and the replacement/root pair all remain
connected to the same certificate throughout the proof. -/
theorem recoverPrefix (xs : Fin 4 → OTerm alpha) (child : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (programGraph lamPath (suc z) xs)))
    (hc : Nonempty (Derivation body Delta
      (programGraph OriginalLambdaGuardLeaf.childCertificate child xs))) :
    Nonempty (Derivation body Delta (graph1 prefixCertificate (xs 2) child)) := by
  let headQuery : Program 4 :=
    .composition InternalListCodec.headCode (fun _ : Fin 1 => path)
  let tailQuery : Program 4 :=
    .composition InternalListCodec.tailCode (fun _ : Fin 1 => path)
  let qs : Fin 4 → Program 4 := ![path,rightOf (.projection 2),headQuery,tailQuery]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  rw [graph1Rename]
  let xx : Fin 4 → OTerm beta := fun i => (xs i).relabel j
  have ha' := renameInto ha j Theta hj
  have hc' := renameInto hc j Theta hj
  simp only [programRename,sucRelabel,zRelabel] at ha' hc'
  have hf := conjunctionRecover pathNonempty pathHeadLambda xx ha'
  have hn := acceptedPathNonzero xx (ys 0) (hq 0) (andLeft hf)
  have hh := acceptedPathHeadZero xx (ys 0) (ys 2) (hq 0) (hq 2) (andRight hf)
  have ht := unaryRecover InternalListCodec.tailCode path (ys 3) (ys 0) xx (hq 3) (hq 0)
  have hcons := InternalListCodecDecompositionSupportProof.reconstructNonzero
    (ys 0) z (ys 3) hn hh ht
  have hl := unaryRecover InternalUnpair.left (.projection 2) (ys 0) (xx 2) xx
    (hq 0) (projectionValue 2 xx)
  have hr := unaryRecover InternalUnpair.right (.projection 2) (ys 1) (xx 2) xx
    (hq 1) (projectionValue 2 xx)
  have hpair := reconstructPair (xx 2) (ys 0) (ys 1) hl hr
  have hstrip := unaryRecover OriginalLambdaGuardLeaf.stripCertificate (.projection 2)
    (child.relabel j) (xx 2) xx hc' (projectionValue 2 xx)
  exact prefixAtFields (xx 2) (child.relabel j) (ys 0) (ys 1) (ys 3) hpair
    (stripAtFields (xx 2) (child.relabel j) (ys 0) (ys 1) (ys 3) hpair ht hstrip) hcons

theorem actualOriginalHereditaryLambdaInternalPrefix :
    OriginalHereditaryLambdaTargets.ActualOriginalHereditaryLambdaInternalPrefix := by
  intro body alpha Delta source target certificate parameter childStep
  let P := accepted lamPath source target certificate parameter ⊓
    graph4 OriginalLambdaGuardLeaf.childCertificate childStep source target certificate parameter
  let xs : Fin 4 → OTerm alpha :=
    Fin.cons source (Fin.cons target (Fin.cons certificate (Fin.cons parameter Fin.elim0)))
  obtain ⟨h⟩ := recoverPrefix (body := body) (Delta := P :: Delta) xs childStep
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixProof
