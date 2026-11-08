module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationCommutationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration InternalNumericIterationSyntaxProof InternalNumericIterationSupportProof
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

theorem succCore (transition : Program 1)
    (count initial next result out : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition count)))
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result (suc count) initial)))
    (ho : Nonempty (Derivation body Gamma (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out (suc count) next)) := by
  apply programCases (repeatProgram transition) (Fin.cons count (Fin.cons initial Fin.elim0)) _
  intro β j Delta tailResult hj ht
  simp only [repeatRename,sucRelabel]
  simp only [consTermRename,emptyRename] at ht
  have hrow' := renameInto hrow j Delta hj
  rw [commuteRowRename] at hrow'
  have hn' := renameInto hn j Delta hj
  simp only [programRename,consTermRename,emptyRename] at hn'
  have hr' := renameInto hr j Delta hj
  simp only [repeatRename,sucRelabel] at hr'
  have ho' := renameInto ho j Delta hj
  simp only [programRename,consTermRename,emptyRename] at ho'
  have hresult := repeatSuccRecover transition (count.relabel j)
    tailResult (result.relabel j) (initial.relabel j) ht hr'
  have htail := rowApply transition (count.relabel j) (initial.relabel j) (next.relabel j)
    tailResult (result.relabel j) hrow' hn' ht hresult
  exact repeatSuccValue transition (count.relabel j)
    (result.relabel j) (out.relabel j) (next.relabel j) htail ho'

theorem succRow (transition : Program 1) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition count))) :
    Nonempty (Derivation body Gamma (commuteRow transition (suc count))) := by
  unfold commuteRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let initial : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let next : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let result : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let c := count.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := programGraph transition next (Fin.cons initial Fin.elim0) ⊓
    (repeatGraph transition result (suc c) initial ⊓
      programGraph transition out (Fin.cons result Fin.elim0))
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [commuteRowRename] at hrow'
  obtain ⟨d⟩ := succCore transition c initial next result out hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [commuteBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Full original arithmetic induction, with four state variables universally
quantified INSIDE the invariant. No standard-model induction is reflected. -/
theorem allRows (transition : Program 1) (count : OTerm α) :
    Nonempty (Derivation body Gamma (commuteRow transition count)) := by
  let theta : Formula (α ⊕ Fin 1) := commuteRow transition (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,commuteInstantiate,varBind] using (zeroRow (body := body) (Gamma := Gamma) transition)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      transition (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,commuteSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,commuteInstantiate,varBind] using (Nonempty.intro h)

theorem commuteValue (transition : Program 1) (code initial next result out : OTerm α)
    (hn : Nonempty (Derivation body Gamma (programGraph transition next (Fin.cons initial Fin.elim0))))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result code initial)))
    (ho : Nonempty (Derivation body Gamma (programGraph transition out (Fin.cons result Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code next)) :=
  rowApply transition code initial next result out (allRows transition code) hn hr ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationCommutationProof
