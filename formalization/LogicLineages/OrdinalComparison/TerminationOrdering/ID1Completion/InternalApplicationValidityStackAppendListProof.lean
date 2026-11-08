module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationValidityStackAppend InternalApplicationCertificateConstructors
open InternalApplicationValidityStackAppendSyntaxProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalRawListRecursion InternalRawListRecursionProof InternalRawListRecursionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionClosureLogicProof InternalRecursionGraphStepSyntaxProof
open InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem appendStepValue (head result suffix out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode out head result))) :
    Nonempty (Derivation body Gamma (graph3 appendStep out head result suffix)) := by
  exact binaryValue InternalListCodec.consCode (.projection 0) (.projection 1) out head result
    (Fin.cons head (Fin.cons result (Fin.cons suffix Fin.elim0))) hc
    (projectionValue 0 (Fin.cons head (Fin.cons result (Fin.cons suffix Fin.elim0))))
    (projectionValue 1 (Fin.cons head (Fin.cons result (Fin.cons suffix Fin.elim0))))

theorem appendZeroValue (suffix : OTerm α) :
    Nonempty (Derivation body Gamma (graph2 append suffix z suffix)) := by
  obtain ⟨heq⟩ := actualOriginalListRecursionZero body 1 (.projection (0 : Fin 1)) appendStep
    α suffix (Fin.cons suffix Fin.elim0)
  exact closedApply ⟨Derivation.conjunctionRight heq⟩ (projectionValue 0 (Fin.cons suffix Fin.elim0))

theorem appendZeroRecover (out suffix : OTerm α)
    (h : Nonempty (Derivation body Gamma (graph2 append out z suffix))) :
    Nonempty (Derivation body Gamma (eqn out suffix)) :=
  valueUnique append out suffix (Fin.cons z (Fin.cons suffix Fin.elim0)) h (appendZeroValue suffix)

theorem consBackward (frontWork head tail suffix result out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode frontWork head tail)))
    (ht : Nonempty (Derivation body Gamma (graph2 append result tail suffix)))
    (ho : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode out head result))) :
    Nonempty (Derivation body Gamma (graph2 append out frontWork suffix)) := by
  obtain ⟨hs⟩ := appendStepValue head result suffix out ho
  obtain ⟨ht⟩ := ht
  have hex : Nonempty (Derivation body Gamma
      (consStep (.projection (0 : Fin 1)) appendStep out head tail (Fin.cons suffix Fin.elim0))) := by
    apply Nonempty.intro
    apply Derivation.existentialIntroduction (emb result)
    rw [consStepInstance]
    exact Derivation.conjunctionIntroduction ht hs
  obtain ⟨heq⟩ := closedApply
    (actualOriginalListRecursionCons body 1 (.projection (0 : Fin 1)) appendStep
      α frontWork head tail out (Fin.cons suffix Fin.elim0)) hc
  obtain ⟨hex⟩ := hex
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight heq) hex⟩

theorem consForward (frontWork head tail suffix result out : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode frontWork head tail)))
    (ht : Nonempty (Derivation body Gamma (graph2 append result tail suffix)))
    (ho : Nonempty (Derivation body Gamma (graph2 append out frontWork suffix))) :
    Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode out head result)) := by
  apply programCases InternalListCodec.consCode (Fin.cons head (Fin.cons result Fin.elim0)) _
  intro β j Delta value hj hv
  rw [graph2Rename]
  simp only [consTermRename,emptyRename] at hv
  have hc' := renameInto hc j Delta hj
  have ht' := renameInto ht j Delta hj
  have ho' := renameInto ho j Delta hj
  simp only [graph2Rename] at hc' ht' ho'
  have ha := consBackward (frontWork.relabel j) (head.relabel j) (tail.relabel j)
    (suffix.relabel j) (result.relabel j) value hc' ht' hv
  exact outputTransport InternalListCodec.consCode value (out.relabel j)
    (Fin.cons (head.relabel j) (Fin.cons (result.relabel j) Fin.elim0))
    (valueUnique append value (out.relabel j)
      (Fin.cons (frontWork.relabel j) (Fin.cons (suffix.relabel j) Fin.elim0)) ha ho') hv

theorem appendConsIntro (out head tail suffix result : OTerm α)
    (ht : Nonempty (Derivation body Gamma (graph2 append result tail suffix)))
    (ho : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode out head result))) :
    Nonempty (Derivation body Gamma (appendConsStep out head tail suffix)) := by
  obtain ⟨ht⟩ := ht
  obtain ⟨ho⟩ := ho
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb result)
  rw [appendConsInstance]
  exact Derivation.conjunctionIntroduction ht ho

theorem appendConsCases (out head tail suffix : OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (appendConsStep out head tail suffix)))
    (k : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (result : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (graph2 append result (tail.relabel j) (suffix.relabel j))) →
      Nonempty (Derivation body Delta
        (graph2 InternalListCodec.consCode (out.relabel j) (head.relabel j) result)) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := graph2 append (.var (.inr (0 : Fin 1)))
      (tail.relabel Sum.inl) (suffix.relabel Sum.inl) ⊓
    graph2 InternalListCodec.consCode (out.relabel Sum.inl)
      (head.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := k (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem actualOriginalRawListAppendZero :
    InternalApplicationValidityStackAppendTargets.ActualOriginalRawListAppendZero := by
  intro body α out suffix
  let P := graph2 append out z suffix
  let Q := equal out suffix
  have hf : Nonempty (Derivation body [P] Q) := by
    change Nonempty (Derivation body [P] (equal out suffix))
    rw [equalEqn]
    exact appendZeroRecover out suffix ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hb : Nonempty (Derivation body [Q] P) := by
    have he : Derivation body [Q] (eqn out suffix) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport append suffix out (Fin.cons z (Fin.cons suffix Fin.elim0))
      ⟨symm he⟩ (appendZeroValue suffix)
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalRawListAppendCons :
    InternalApplicationValidityStackAppendTargets.ActualOriginalRawListAppendCons := by
  intro body α frontWork head tail suffix out
  let A := graph2 InternalListCodec.consCode frontWork head tail
  let P := graph2 append out frontWork suffix
  let Q := appendConsStep out head tail suffix
  have hf : Nonempty (Derivation body [P,A] Q) := by
    apply programCases append (Fin.cons tail (Fin.cons suffix Fin.elim0)) _
    intro β j Delta result hj hr
    rw [appendConsRename]
    simp only [consTermRename,emptyRename] at hr
    have hc := renameInto (body := body) (Nonempty.intro (Derivation.hypothesis
      (Gamma := [P,A]) (List.mem_cons_of_mem _ List.mem_cons_self))) j Delta hj
    have ho := renameInto (body := body) (Nonempty.intro (Derivation.hypothesis
      (Gamma := [P,A]) List.mem_cons_self)) j Delta hj
    simp only [A,P,graph2Rename] at hc ho
    exact appendConsIntro (out.relabel j) (head.relabel j) (tail.relabel j)
      (suffix.relabel j) result hr
      (consForward (frontWork.relabel j) (head.relabel j) (tail.relabel j)
        (suffix.relabel j) result (out.relabel j) hc hr ho)
  have hb : Nonempty (Derivation body [Q,A] P) := by
    apply appendConsCases out head tail suffix _ ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro β j Delta result hj hr hc
    simp only [P,graph2Rename]
    have ha := renameInto (body := body) (Nonempty.intro (Derivation.hypothesis
      (Gamma := [Q,A]) (List.mem_cons_of_mem _ List.mem_cons_self))) j Delta hj
    simp only [A,graph2Rename] at ha
    exact consBackward (frontWork.relabel j) (head.relabel j) (tail.relabel j)
      (suffix.relabel j) result (out.relabel j) ha hr hc
  obtain ⟨hf⟩ := hf
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
