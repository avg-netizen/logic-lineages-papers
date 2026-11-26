module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNilNormalizationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepRunProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNilNormalizationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z zRelabel)
open OriginalTransparentLambdaStep OriginalHereditaryLambdaChildStateProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem runAtNil (source : Program 2) (state s t cert parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)))
    (hl : Nonempty (Derivation body Delta (graph4 OriginalHereditaryLambda.live state s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 (run source) state s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  have hpath := unaryValue InternalUnpair.left (.projection 2) z cert xs hp (projectionValue 2 xs)
  exact binaryValue (InternalRawListRepeat.repeatProgram (transition source))
    OriginalHereditaryLambda.path OriginalHereditaryLambda.live state z state xs
    (InternalRawListRepeatSupportProof.repeatZeroValue (transition source) state) hpath hl

theorem introduction (source : Program 2) (oldStep : Program 4)
    (out s t cert parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)))
    (ho : Nonempty (Derivation body Delta (graph4 oldStep out s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 (refined source oldStep) out s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  apply programCases OriginalHereditaryLambda.live xs _
  intro beta j Gamma state hj hl
  have hx : (fun i => (xs i).relabel j) =
      Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
        (Fin.cons (cert.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
  rw [hx] at hl
  rw [graph4Rename]
  have hp' := renameInto hp j Gamma hj
  have ho' := renameInto ho j Gamma hj
  simp only [graph1Rename,zRelabel] at hp'
  rw [graph4Rename] at ho'
  have hr := runAtNil source state (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j) hp' hl
  have ht := atLiveValue oldStep (out.relabel j) state (s.relabel j) (t.relabel j)
    (cert.relabel j) (parameter.relabel j) hl ho'
  exact unaryValue (OriginalHereditaryLambda.atState oldStep) (run source) (out.relabel j) state
    (Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
      (Fin.cons (cert.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))) ht hr

theorem elimination (source : Program 2) (oldStep : Program 4)
    (out s t cert parameter : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left z cert)))
    (ho : Nonempty (Derivation body Delta (graph4 (refined source oldStep) out s t cert parameter))) :
    Nonempty (Derivation body Delta (graph4 oldStep out s t cert parameter)) := by
  let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
  apply programCases OriginalHereditaryLambda.live xs _
  intro beta j Gamma state hj hl
  have hx : (fun i => (xs i).relabel j) =
      Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
        (Fin.cons (cert.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0))) := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)))) i
  rw [hx] at hl
  rw [graph4Rename]
  have hp' := renameInto hp j Gamma hj
  have ho' := renameInto ho j Gamma hj
  simp only [graph1Rename,zRelabel] at hp'
  rw [graph4Rename] at ho'
  have hr := runAtNil source state (s.relabel j) (t.relabel j) (cert.relabel j) (parameter.relabel j) hp' hl
  have ht := unaryRecover (OriginalHereditaryLambda.atState oldStep) (run source) (out.relabel j) state
    (Fin.cons (s.relabel j) (Fin.cons (t.relabel j)
      (Fin.cons (cert.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))) ho' hr
  exact atLiveRecover oldStep (out.relabel j) state (s.relabel j) (t.relabel j)
    (cert.relabel j) (parameter.relabel j) hl ht

theorem actualOriginalTransparentLambdaStepNilNormalization :
    OriginalTransparentLambdaStepNilNormalizationTargets.ActualOriginalTransparentLambdaStepNilNormalization := by
  intro source oldStep body alpha Delta out s t cert parameter
  let A := graph1 InternalUnpair.left z cert
  let P := graph4 (refined source oldStep) out s t cert parameter
  let Q := graph4 oldStep out s t cert parameter
  have hp : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hf⟩ := elimination source oldStep out s t cert parameter (withHyp hp P)
    (show Nonempty (Derivation body (P :: A :: Delta) P) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨hb⟩ := introduction source oldStep out s t cert parameter (withHyp hp Q)
    (show Nonempty (Derivation body (Q :: A :: Delta) Q) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNilNormalizationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNilNormalizationProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepNilNormalizationProof.actualOriginalTransparentLambdaStepNilNormalization
