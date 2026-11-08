module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatCommutationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRepeat InternalRawListRepeatSyntaxProof InternalRawListRepeatSupportProof
open InternalListCodec InternalListCodecSupportProof InternalListInduction InternalListInductionProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (transition : Program 1) (code initial next result out : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition code)))
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result code initial)))
    (ho : Nonempty (Derivation body Gamma (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code next)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (commuteBody transition code)
    (fun i => emb (![initial,next,result,out] i)) hrow
  rw [commuteBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hn⟩ := hn
  obtain ⟨hr⟩ := hr
  obtain ⟨ho⟩ := ho
  exact ⟨Derivation.implicationElimination h
    (Derivation.conjunctionIntroduction hn (Derivation.conjunctionIntroduction hr ho))⟩

theorem zeroCore (transition : Program 1) (initial next result out : OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result z initial)))
    (ho : Nonempty (Derivation body Gamma (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out z next)) := by
  have he := repeatZeroRecover transition result initial hr
  have ho' := headTransport transition out result initial Fin.elim0 he ho
  have hnout := valueUnique transition next out (Fin.cons initial Fin.elim0) hn ho'
  exact outputTransport (repeatProgram transition) next out
    (Fin.cons z (Fin.cons next Fin.elim0)) hnout (repeatZeroValue transition next)

theorem zeroRow (transition : Program 1) :
    Nonempty (Derivation body Gamma (commuteRow transition z)) := by
  unfold commuteRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let initial : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let next : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let result : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := programGraph transition next (Fin.cons initial Fin.elim0) ⊓
    (repeatGraph transition result z initial ⊓
      programGraph transition out (Fin.cons result Fin.elim0))
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) transition initial next result out
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [commuteBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem consCore (transition : Program 1)
    (code head tail initial next result out : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result code initial)))
    (ho : Nonempty (Derivation body Gamma (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code next)) := by
  apply programCases (repeatProgram transition) (Fin.cons tail (Fin.cons initial Fin.elim0)) _
  intro β j Delta tailResult hj ht
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at ht
  have hrow' := renameInto hrow j Delta hj
  rw [commuteRowRename] at hrow'
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hn' := renameInto hn j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hn'
  have hr' := renameInto hr j Delta hj
  rw [repeatRename] at hr'
  have ho' := renameInto ho j Delta hj
  simp only [programRename,consTermRename,emptyRename] at ho'
  have hresult := repeatConsRecover transition (code.relabel j) (head.relabel j) (tail.relabel j)
    tailResult (result.relabel j) (initial.relabel j) hc' ht hr'
  have htail := rowApply transition (tail.relabel j) (initial.relabel j) (next.relabel j)
    tailResult (result.relabel j) hrow' hn' ht hresult
  exact repeatConsValue transition (code.relabel j) (head.relabel j) (tail.relabel j)
    (result.relabel j) (out.relabel j) (next.relabel j) hc' htail ho'

theorem consRow (transition : Program 1) (code head tail : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail))) :
    Nonempty (Derivation body Gamma (commuteRow transition code)) := by
  unfold commuteRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let initial : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let next : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let result : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let c := code.relabel (Sum.inl : α → α ⊕ Fin 4)
  let h := head.relabel (Sum.inl : α → α ⊕ Fin 4)
  let t := tail.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := programGraph transition next (Fin.cons initial Fin.elim0) ⊓
    (repeatGraph transition result c initial ⊓
      programGraph transition out (Fin.cons result Fin.elim0))
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [commuteRowRename] at hrow'
  have hc' := renameInto hc Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [consGraphRename] at hc'
  obtain ⟨d⟩ := consCore transition c h t initial next result out hrow' hc'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Invoke the proved full-language list-code induction schema, with all
four state variables quantified inside the invariant. -/
theorem allRows (transition : Program 1) (code : OTerm α) :
    Nonempty (Derivation body Gamma (commuteRow transition code)) := by
  let theta : Formula (α ⊕ Fin 1) := commuteRow transition (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (atCode theta z)) := by
    rw [commuteAtCode]
    exact zeroRow transition
  have hs : Nonempty (Derivation body Gamma (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body α 3 Gamma
    simp only [constructorBody,theta,commuteAtIndex]
    let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
    let C := consGraph c h t
    let R := commuteRow transition t
    obtain ⟨d⟩ := consRow (body := body)
      (Gamma := R :: C :: Gamma.map (fun p => p.relabel Sum.inl)) transition c h t
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := actualOriginalListInductionAtCode body α Gamma theta code
    ⟨Derivation.conjunctionIntroduction hz hs⟩
  rw [commuteAtCode] at h
  exact h

theorem commuteValue (transition : Program 1) (code initial next result out : OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result code initial)))
    (ho : Nonempty (Derivation body Gamma (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code next)) :=
  rowApply transition code initial next result out (allRows transition code) hn hr ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatCommutationProof
