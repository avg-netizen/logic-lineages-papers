module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatCommutationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalParameterizedApplicationStepChecker
open InternalParameterizedApplicationStepCheckerRepeatSyntaxProof
open InternalParameterizedApplicationStepCheckerRepeatSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalListCodec InternalListCodecSupportProof InternalListInduction InternalListInductionProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (transition : Program 2) (code initial next result out parameter : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition code)))
    (hn : Nonempty (Derivation body Gamma (graph2 transition next initial parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result code initial parameter)))
    (ho : Nonempty (Derivation body Gamma (graph2 transition out result parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code next parameter)) := by
  have h := actualFiniteUniversalElimination body α 5 Gamma (commuteBody transition code)
    (fun i => emb (![initial,next,result,out,parameter] i)) hrow
  rw [commuteBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hn⟩ := hn
  obtain ⟨hr⟩ := hr
  obtain ⟨ho⟩ := ho
  exact ⟨Derivation.implicationElimination h
    (Derivation.conjunctionIntroduction hn (Derivation.conjunctionIntroduction hr ho))⟩

theorem zeroCore (transition : Program 2) (initial next result out parameter : OTerm α)
    (hn : Nonempty (Derivation body Gamma (graph2 transition next initial parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result z initial parameter)))
    (ho : Nonempty (Derivation body Gamma (graph2 transition out result parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out z next parameter)) := by
  have he := repeatZeroRecover transition result initial parameter hr
  have ho' := headTransport transition out result initial (Fin.cons parameter Fin.elim0) he ho
  have hnout := valueUnique transition next out (Fin.cons initial (Fin.cons parameter Fin.elim0)) hn ho'
  exact outputTransport (repeatP transition) next out
    (Fin.cons z (Fin.cons next (Fin.cons parameter Fin.elim0))) hnout
    (repeatZeroValue transition next parameter)

theorem zeroRow (transition : Program 2) :
    Nonempty (Derivation body Gamma (commuteRow transition z)) := by
  unfold commuteRow
  apply actualFiniteUniversalIntroduction body α 5 Gamma
  let initial : OTerm (α ⊕ Fin 5) := .var (.inr 0)
  let next : OTerm (α ⊕ Fin 5) := .var (.inr 1)
  let result : OTerm (α ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 5) := .var (.inr 3)
  let parameter : OTerm (α ⊕ Fin 5) := .var (.inr 4)
  let A := graph2 transition next initial parameter ⊓
    (repeatGraph transition result z initial parameter ⊓ graph2 transition out result parameter)
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl))
    transition initial next result out parameter
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [commuteBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem consCore (transition : Program 2)
    (code head tail initial next result out parameter : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail)))
    (hn : Nonempty (Derivation body Gamma (graph2 transition next initial parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result code initial parameter)))
    (ho : Nonempty (Derivation body Gamma (graph2 transition out result parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code next parameter)) := by
  apply programCases (repeatP transition) (Fin.cons tail (Fin.cons initial (Fin.cons parameter Fin.elim0))) _
  intro β j Delta tailResult hj ht
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at ht
  have hrow' := renameInto hrow j Delta hj
  rw [commuteRowRename] at hrow'
  have hc' := renameInto hc j Delta hj
  rw [consGraphRename] at hc'
  have hn' := renameInto hn j Delta hj
  rw [graph2Rename] at hn'
  have hr' := renameInto hr j Delta hj
  rw [repeatRename] at hr'
  have ho' := renameInto ho j Delta hj
  rw [graph2Rename] at ho'
  have hresult := repeatConsRecover transition (code.relabel j) (head.relabel j) (tail.relabel j)
    tailResult (result.relabel j) (initial.relabel j) (parameter.relabel j) hc' ht hr'
  have htail := rowApply transition (tail.relabel j) (initial.relabel j) (next.relabel j)
    tailResult (result.relabel j) (parameter.relabel j) hrow' hn' ht hresult
  exact repeatConsValue transition (code.relabel j) (head.relabel j) (tail.relabel j)
    (result.relabel j) (out.relabel j) (next.relabel j) (parameter.relabel j) hc' htail ho'

theorem consRow (transition : Program 2) (code head tail : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (commuteRow transition tail)))
    (hc : Nonempty (Derivation body Gamma (consGraph code head tail))) :
    Nonempty (Derivation body Gamma (commuteRow transition code)) := by
  unfold commuteRow
  apply actualFiniteUniversalIntroduction body α 5 Gamma
  let initial : OTerm (α ⊕ Fin 5) := .var (.inr 0)
  let next : OTerm (α ⊕ Fin 5) := .var (.inr 1)
  let result : OTerm (α ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 5) := .var (.inr 3)
  let parameter : OTerm (α ⊕ Fin 5) := .var (.inr 4)
  let c := code.relabel (Sum.inl : α → α ⊕ Fin 5)
  let h := head.relabel (Sum.inl : α → α ⊕ Fin 5)
  let t := tail.relabel (Sum.inl : α → α ⊕ Fin 5)
  let A := graph2 transition next initial parameter ⊓
    (repeatGraph transition result c initial parameter ⊓ graph2 transition out result parameter)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 5))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [commuteRowRename] at hrow'
  have hc' := renameInto hc Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [consGraphRename] at hc'
  obtain ⟨d⟩ := consCore transition c h t initial next result out parameter hrow' hc'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  exact ⟨Derivation.implicationIntroduction d⟩

/-- Apply the existing full-language original list-code induction with all
five variables quantified inside its invariant. The parameter is never fuel. -/
theorem allRows (transition : Program 2) (code : OTerm α) :
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

theorem commuteValue (transition : Program 2) (code initial next result out parameter : OTerm α)
    (hn : Nonempty (Derivation body Gamma (graph2 transition next initial parameter)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph transition result code initial parameter)))
    (ho : Nonempty (Derivation body Gamma (graph2 transition out result parameter))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out code next parameter)) :=
  rowApply transition code initial next result out parameter (allRows transition code) hn hr ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatCommutationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedApplicationStepCheckerRepeatCommutationProof
