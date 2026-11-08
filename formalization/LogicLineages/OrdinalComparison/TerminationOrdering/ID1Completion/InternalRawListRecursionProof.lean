module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionTableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionNextProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRecursion InternalRawListRecursionSyntaxProof InternalRawListRecursionSupportProof
open InternalRawListRecursionTableProof InternalRawListRecursionNextProof
open InternalListCodec SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalListCodecSupportProof InternalListCodecDecompositionSupportProof
open InternalPositiveUnfoldingSupportProof InternalAdditionLawsProof InternalOriginalOrderSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem nilValue {k : Nat} (base : Program k) (step : Program (k + 2))
    (out : OTerm α) (params : Fin k → OTerm α)
    (h : Nonempty (Derivation body Gamma (programGraph base out params))) :
    Nonempty (Derivation body Gamma (recGraph base step out z params)) := by
  apply programCases consCode (Fin.cons out (Fin.cons z Fin.elim0)) _
  intro β j Delta tab hj hc
  simp only [recRename,zRelabel]
  simp only [consTermRename,zRelabel,emptyRename] at hc
  have h' := renameInto h j Delta hj
  rw [programRename] at h'
  have ht := tableZeroValue base step (out.relabel j) tab (fun i => (params i).relabel j) h' hc
  exact recValue base step (out.relabel j) z tab (fun i => (params i).relabel j) ht
    (consHead tab (out.relabel j) z hc)

theorem nilRecover {k : Nat} (base : Program k) (step : Program (k + 2))
    (out : OTerm α) (params : Fin k → OTerm α)
    (h : Nonempty (Derivation body Gamma (recGraph base step out z params))) :
    Nonempty (Derivation body Gamma (programGraph base out params)) := by
  apply programCases base params _
  intro β j Delta value hj hv
  rw [programRename]
  have h' := renameInto h j Delta hj
  simp only [recRename,zRelabel] at h'
  obtain ⟨he⟩ := valueUnique (listRec base step) value (out.relabel j)
    (Fin.cons z (fun i => (params i).relabel j))
    (nilValue base step value (fun i => (params i).relabel j) hv) h'
  exact outputTransport base value (out.relabel j) (fun i => (params i).relabel j) ⟨he⟩ hv

theorem successorValue {k : Nat} (base : Program k) (step : Program (k + 2))
    (out index previous : OTerm α) (params : Fin k → OTerm α)
    (hp : Nonempty (Derivation body Gamma (tableGraph base step previous index params)))
    (hv : Nonempty (Derivation body Gamma (programGraph (nextValue step) out
      (Fin.cons index (Fin.cons previous params))))) :
    Nonempty (Derivation body Gamma (recGraph base step out (suc index) params)) := by
  apply programCases consCode (Fin.cons out (Fin.cons previous Fin.elim0)) _
  intro β j Delta tab hj hc
  simp only [recRename,sucRelabel]
  simp only [consTermRename,emptyRename] at hc
  have hp' := renameInto hp j Delta hj
  rw [tableRename] at hp'
  have hv' := renameInto hv j Delta hj
  simp only [programRename,consTermRename] at hv'
  have ht := tableNext base step (out.relabel j) tab (index.relabel j) (previous.relabel j)
    (fun i => (params i).relabel j) hp' hv' hc
  exact recValue base step (out.relabel j) (suc (index.relabel j)) tab
    (fun i => (params i).relabel j) ht (consHead tab (out.relabel j) (previous.relabel j) hc)

theorem consAtGap {k : Nat} (base : Program k) (step : Program (k + 2))
    (head tail gap result out : OTerm α) (params : Fin k → OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph (suc (add tail gap)) head tail)))
    (hr : Nonempty (Derivation body Gamma (recGraph base step result tail params)))
    (hs : Nonempty (Derivation body Gamma (programGraph step out (Fin.cons head (Fin.cons result params))))) :
    Nonempty (Derivation body Gamma (recGraph base step out (suc (add tail gap)) params)) := by
  apply programCases (table base step) (Fin.cons (add tail gap) params) _
  intro β j Delta previous hj hp
  simp only [recRename,sucRelabel,addRelabel]
  simp only [consTermRename,addRelabel] at hp
  have hc' := renameInto hc j Delta hj
  simp only [consGraphRename,sucRelabel,addRelabel] at hc'
  have hr' := renameInto hr j Delta hj
  rw [recRename] at hr'
  have hs' := renameInto hs j Delta hj
  simp only [programRename,consTermRename] at hs'
  let h := head.relabel j
  let t := tail.relabel j
  let g := gap.relabel j
  let r := result.relabel j
  let o := out.relabel j
  let ps := fun i => (params i).relabel j
  have hh := consHead (suc (add t g)) h t hc'
  have ht := consTail (suc (add t g)) h t hc'
  have hd := InternalEqualityTestSubtractionProof.diagonal (body := body) (Gamma := Delta) t g
  have hl := tableLookup base step r t g previous ps hr' hp
  have hn := nextValueAt step (add t g) previous h t g r o ps hh ht hd hl hs'
  exact successorValue base step o (add t g) previous ps hp hn

/-- Strict descent of the original tail supplies the difference witness
needed by the literal table lookup and subtraction programs. -/
theorem consValue {k : Nat} (base : Program k) (step : Program (k + 2))
    (code head tail result out : OTerm α) (params : Fin k → OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hr : Nonempty (Derivation body Gamma (recGraph base step result tail params)))
    (hs : Nonempty (Derivation body Gamma (programGraph step out (Fin.cons head (Fin.cons result params))))) :
    Nonempty (Derivation body Gamma (recGraph base step out code params)) := by
  have ht := consTailDescent code head tail hc
  apply InternalOriginalOrderProof.orderCases Gamma tail code _ ht
  intro β j Delta gap hj he
  rw [recRename]
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hr' := renameInto hr j Delta hj
  rw [recRename] at hr'
  have hs' := renameInto hs j Delta hj
  simp only [programRename,consTermRename] at hs'
  obtain ⟨he⟩ := he
  let t := tail.relabel j
  have hn : Derivation body Delta (eqn (suc (add t gap)) (code.relabel j)) :=
    trans (symm (addSucc t gap)) he
  have hc'' := outputTransport consCode (code.relabel j) (suc (add t gap))
    (Fin.cons (head.relabel j) (Fin.cons t Fin.elim0)) ⟨symm hn⟩ hc'
  have hrec := consAtGap base step (head.relabel j) t gap (result.relabel j)
    (out.relabel j) (fun i => (params i).relabel j) hc'' hr' hs'
  exact headTransport (listRec base step) (out.relabel j) (suc (add t gap)) (code.relabel j)
    (fun i => (params i).relabel j) ⟨hn⟩ hrec

theorem stepIntroduction {k : Nat} (base : Program k) (step : Program (k + 2))
    (out head tail result : OTerm α) (params : Fin k → OTerm α)
    (hr : Nonempty (Derivation body Gamma (recGraph base step result tail params)))
    (hs : Nonempty (Derivation body Gamma (programGraph step out (Fin.cons head (Fin.cons result params))))) :
    Nonempty (Derivation body Gamma (consStep base step out head tail params)) := by
  obtain ⟨hr⟩ := hr
  obtain ⟨hs⟩ := hs
  apply Nonempty.intro
  apply Derivation.existentialIntroduction (emb result)
  rw [consStepInstance]
  exact Derivation.conjunctionIntroduction hr hs

theorem stepCases {k : Nat} (base : Program k) (step : Program (k + 2))
    (out head tail : OTerm α) (params : Fin k → OTerm α) (psi : Formula α)
    (h : Nonempty (Derivation body Gamma (consStep base step out head tail params)))
    (next : ∀ (β : Type) (j : α → β) (Delta : List (Formula β)) (result : OTerm β),
      (∀ p ∈ Gamma, p.relabel j ∈ Delta) →
      Nonempty (Derivation body Delta (recGraph base step result (tail.relabel j)
        (fun i => (params i).relabel j))) →
      Nonempty (Derivation body Delta (programGraph step (out.relabel j)
        (Fin.cons (head.relabel j) (Fin.cons result (fun i => (params i).relabel j))))) →
      Nonempty (Derivation body Delta (psi.relabel j))) :
    Nonempty (Derivation body Gamma psi) := by
  obtain ⟨h⟩ := h
  let P := recGraph base step (.var (.inr (0 : Fin 1))) (tail.relabel Sum.inl)
      (fun i => (params i).relabel Sum.inl) ⊓
    programGraph step (out.relabel Sum.inl)
      (Fin.cons (head.relabel Sum.inl) (Fin.cons (.var (.inr 0)) (fun i => (params i).relabel Sum.inl)))
  let Delta := P :: Gamma.map weaken
  obtain ⟨d⟩ := next (α ⊕ Fin 1) Sum.inl Delta (.var (.inr 0))
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.existentialElimination h d⟩

theorem consForward {k : Nat} (base : Program k) (step : Program (k + 2))
    (code head tail out : OTerm α) (params : Fin k → OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (h : Nonempty (Derivation body Gamma (recGraph base step out code params))) :
    Nonempty (Derivation body Gamma (consStep base step out head tail params)) := by
  apply programCases (listRec base step) (Fin.cons tail params) _
  intro β j Delta result hj hr
  rw [consStepRename]
  simp only [consTermRename] at hr
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have h' := renameInto h j Delta hj
  rw [recRename] at h'
  apply programCases step
    (Fin.cons (head.relabel j) (Fin.cons result (fun i => (params i).relabel j))) _
  intro γ l Theta value hl hs
  rw [consStepRename]
  simp only [consTermRename] at hs
  have hc'' := renameInto hc' l Theta hl
  rw [consGraphRename] at hc''
  have h'' := renameInto h' l Theta hl
  rw [recRename] at h''
  have hr' := renameInto hr l Theta hl
  simp only [programRename,consTermRename] at hr'
  let ps := fun i => ((params i).relabel j).relabel l
  have hv := consValue base step ((code.relabel j).relabel l) ((head.relabel j).relabel l)
    ((tail.relabel j).relabel l) (result.relabel l) value ps hc'' hr' hs
  have he := valueUnique (listRec base step) value ((out.relabel j).relabel l)
    (Fin.cons ((code.relabel j).relabel l) ps) hv h''
  have hs' := outputTransport step value ((out.relabel j).relabel l)
    (Fin.cons ((head.relabel j).relabel l) (Fin.cons (result.relabel l) ps)) he hs
  exact stepIntroduction base step ((out.relabel j).relabel l) ((head.relabel j).relabel l)
    ((tail.relabel j).relabel l) (result.relabel l) ps hr' hs'

theorem consBackward {k : Nat} (base : Program k) (step : Program (k + 2))
    (code head tail out : OTerm α) (params : Fin k → OTerm α)
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (h : Nonempty (Derivation body Gamma (consStep base step out head tail params))) :
    Nonempty (Derivation body Gamma (recGraph base step out code params)) := by
  apply stepCases base step out head tail params _ h
  intro β j Delta result hj hr hs
  rw [recRename]
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  exact consValue base step (code.relabel j) (head.relabel j) (tail.relabel j) result
    (out.relabel j) (fun i => (params i).relabel j) hc' hr hs

theorem actualOriginalListRecursionZero : InternalRawListRecursionTargets.ActualOriginalListRecursionZero := by
  intro body k base step α out params
  obtain ⟨forward⟩ := nilRecover (body := body) base step out params
    (show Nonempty (Derivation body [recGraph base step out z params] _) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  obtain ⟨backward⟩ := nilValue (body := body) base step out params
    (show Nonempty (Derivation body [programGraph base out params] _) from
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

theorem actualOriginalListRecursionCons : InternalRawListRecursionTargets.ActualOriginalListRecursionCons := by
  intro body k base step α code head tail out params
  let C := consGraph code head tail
  let R := recGraph base step out code params
  let S := consStep base step out head tail params
  obtain ⟨forward⟩ := consForward (body := body) (Gamma := [R,C]) base step code head tail out params
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨backward⟩ := consBackward (body := body) (Gamma := [S,C]) base step code head tail out params
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
      (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
