module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildControlProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRepeatSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaPrefixSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open OriginalHereditaryLambda OriginalHereditaryLambdaChildStateProof OriginalHereditaryLambdaChildControlProof
open OriginalHereditaryLambdaPrefixSupportProof OriginalHereditaryLambdaRepeatSupportProof
open OriginalLambdaGuardLeafInternalProof (combine projectLeft projectRight)
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof InternalAcceptanceConjunctionProof
open InternalControlGraphSupportProof InternalTagArithmeticSupportProof InternalBetaTotalityProof
open InternalRecursionGraphStepSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalRawListRepeat InternalRawListRepeatSupportProof InternalRawListRepeatSyntaxProof
open InternalApplicationStepPeelSupportProof (queryCases)
open InternalTagArithmeticSyntaxProof (z suc eqn eqnRelabel zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- An accepting run cannot start at the absorbing failure state. -/
theorem acceptingRunNonzero (oldStep : Program 4) (out code state : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (repeatGraph (transition oldStep) out code state)))
    (hf : Nonempty (Derivation body Delta (graph1 finish (suc z) out))) :
    Nonempty (Derivation body Delta (eqn state z).not) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hf⟩ := hf
  let P := eqn state z
  have hz := fixedValue (body := body) (Gamma := P :: Delta) (transition oldStep) z code
    (transitionZero oldStep)
  have hstate : Nonempty (Derivation body (P :: Delta)
      (repeatGraph (transition oldStep) z code state)) := by
    apply InternalGraphCompositionEqualityProof.graphInputTransport body alpha 2 (P :: Delta)
      (OrdinaryArithmetic.graphFormula (repeatProgram (transition oldStep))) z
      (Fin.cons code (Fin.cons z Fin.elim0)) (Fin.cons code (Fin.cons state Fin.elim0)) _ hz
    intro i
    rw [InternalSourceInversionSupportProof.onEquality]
    exact Fin.cases ⟨refl code⟩ (Fin.cases
      ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (fun k => Fin.elim0 k)) i
  obtain ⟨he⟩ := valueUnique (repeatProgram (transition oldStep)) out z
    (Fin.cons code (Fin.cons state Fin.elim0)) ⟨addHyp hr P⟩ hstate
  have hfinish := headTransport finish (suc z) out z Fin.elim0 ⟨he⟩ ⟨addHyp hf P⟩
  obtain ⟨hzf⟩ := valueUnique finish (suc z) z (Fin.cons z Fin.elim0) hfinish finishZero
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hzf)⟩

/-- An active original source cannot accept without a literal path cell. -/
theorem activeRunPathNonzero (oldStep : Program 4)
    (out code state source target certificate parameter : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (graph4 live state source target certificate parameter)))
    (ha : Nonempty (Derivation body Delta (LambdaNonbottom source target certificate parameter)))
    (hr : Nonempty (Derivation body Delta (repeatGraph (transition oldStep) out code state)))
    (hf : Nonempty (Derivation body Delta (graph1 finish (suc z) out))) :
    Nonempty (Derivation body Delta (eqn code z).not) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hf⟩ := hf
  obtain ⟨hactive⟩ := finishActive state source target certificate parameter hl ha
  let P := eqn code z
  have hz := headTransport (repeatProgram (transition oldStep)) out code z
    (Fin.cons state Fin.elim0) ⟨Derivation.hypothesis List.mem_cons_self⟩ ⟨addHyp hr P⟩
  have he := repeatZeroRecover (transition oldStep) out state hz
  have hh := headTransport finish (suc z) out state Fin.elim0 he ⟨addHyp hf P⟩
  obtain ⟨hbad⟩ := valueUnique finish (suc z) z (Fin.cons state Fin.elim0)
    hh ⟨addHyp hactive P⟩
  exact ⟨Derivation.implicationIntroduction (sucNeZeroApply hbad)⟩

/-- The actual stripped certificate has the literal original path tail. Its
replacement/root payload is obtained internally and never altered. -/
theorem strippedPath (xs : Fin 4 → OTerm alpha) (child code tail : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path code xs)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail code)))
    (hc : Nonempty (Derivation body Delta
      (programGraph OriginalLambdaGuardLeaf.childCertificate child xs))) :
    Nonempty (Derivation body Delta (graph1 InternalUnpair.left tail child)) := by
  apply programCases InternalUnpair.right (Fin.cons (xs 2) Fin.elim0) _
  intro beta j Theta payload hj hright
  rw [graph1Rename]
  have hp' := renameInto hp j Theta hj
  have ht' := renameInto ht j Theta hj
  have hc' := renameInto hc j Theta hj
  rw [graph1Rename] at ht'
  simp only [programRename] at hp' hc'
  simp only [consTermRename,emptyRename] at hright
  let xx := fun i => (xs i).relabel j
  have hleft := unaryRecover InternalUnpair.left (.projection 2) (code.relabel j) (xx 2) xx
    hp' (projectionValue 2 xx)
  have hpair := reconstructPair (xx 2) (code.relabel j) payload hleft hright
  have hstrip := unaryRecover OriginalLambdaGuardLeaf.stripCertificate (.projection 2)
    (child.relabel j) (xx 2) xx hc' (projectionValue 2 xx)
  exact pairLeft (child.relabel j) (tail.relabel j) payload
    (stripAtFields (xx 2) (child.relabel j) (code.relabel j) payload (tail.relabel j)
      hpair ht' hstrip)

/-- The old child acceptance and the SAME tail run produce acceptance by the
SAME refined AST at the actual child tuple. The selector block remains bound
by the original composition graph throughout. -/
theorem hereditaryChildCheck (oldStep : Program 4) (xs : Fin 4 → OTerm alpha)
    (code tail next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph path code xs)))
    (ht : Nonempty (Derivation body Delta (graph1 InternalListCodec.tailCode tail code)))
    (hc : Nonempty (Derivation body Delta
      (programGraph (OriginalLambdaGuardLeaf.childCheck oldStep) (suc z) xs)))
    (hl : Nonempty (Derivation body Delta (programGraph childLive next xs)))
    (hr : Nonempty (Derivation body Delta (repeatGraph (transition oldStep) out tail next)))
    (hf : Nonempty (Derivation body Delta (graph1 finish (suc z) out))) :
    Nonempty (Derivation body Delta
      (programGraph (OriginalLambdaGuardLeaf.childCheck (refined oldStep)) (suc z) xs)) := by
  let qs : Fin 4 → Program 4 := ![OriginalLambdaGuardLeaf.sourceBody,OriginalLambdaGuardLeaf.targetBody,
    OriginalLambdaGuardLeaf.childCertificate,OriginalLambdaGuardLeaf.childParameter]
  apply programCompositionCases oldStep qs (suc z) xs _ hc
  intro beta j ys Theta hj hold hg
  simp only [programRename,sucRelabel,zRelabel]
  have hp' := renameInto hp j Theta hj
  have ht' := renameInto ht j Theta hj
  have hl' := renameInto hl j Theta hj
  have hr' := renameInto hr j Theta hj
  have hf' := renameInto hf j Theta hj
  rw [graph1Rename] at ht' hf'
  rw [repeatRename] at hr'
  simp only [programRename] at hp' hl'
  simp only [sucRelabel,zRelabel] at hf' hold
  let xx := fun i => (xs i).relabel j
  have hchildLive := compositionRecover live qs (next.relabel j) xx ys hl' hg
  have hleft := strippedPath xx (ys 2) (code.relabel j) (tail.relabel j) hp' ht' (hg 2)
  have hchildPath := unaryValue InternalUnpair.left (.projection 2) (tail.relabel j) (ys 2) ys
    hleft (projectionValue 2 ys)
  have hrun := binaryValue (repeatProgram (transition oldStep)) path live (out.relabel j)
    (tail.relabel j) (next.relabel j) ys hr' hchildPath hchildLive
  have hguard := unaryValue finish (run oldStep) (suc z) (out.relabel j) ys hf' hrun
  have hrefined := conjunctionAccept oldStep (guard oldStep) ys hold hguard
  exact compositionValue (refined oldStep) qs (suc z) xx ys hrefined hg

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaChildRunProof
