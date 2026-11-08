module
public import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationCarryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationCommutationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalParameterizedNumericIteration InternalParameterizedNumericIterationCarryProof
open InternalNumericIterationSyntaxProof InternalNumericIterationSupportProof
open InternalRawListRecursionSyntaxProof
open InternalListInduction InternalListInductionProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalAdditionLawsProof (impSubst)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

def preserveBody {α : Type} (P : Program 2) (count : OTerm α) : Formula (α ⊕ Fin 3) :=
  (graph1 InternalUnpair.left (.var (.inr 2)) (.var (.inr 0)) ⊓
    InternalNumericIteration.repeatGraph (carryP P) (.var (.inr 1))
      (count.relabel Sum.inl) (.var (.inr 0))).imp
    (graph1 InternalUnpair.left (.var (.inr 2)) (.var (.inr 1)))
def preserveRow {α : Type} (P : Program 2) (count : OTerm α) : Formula α :=
  allBlock (preserveBody P count)

theorem preserveRowSubst {α β : Type} (P : Program 2) (count : OTerm α) (ts : α → OTerm β) :
    (preserveRow P count).subst (fun a => emb (ts a)) = preserveRow P (count.subst ts) := by
  unfold preserveRow preserveBody graph1
  rw [allBlockSubst,liftedEmbedding,impSubst,conjunctionSubst]
  simp only [programSubst,repeatSubst,consTermSubst,liftSubst,Term.subst,Sum.elim_inr,emptySubst]

theorem preserveRowRename {α β : Type} (P : Program 2) (count : OTerm α) (j : α → β) :
    (preserveRow P count).relabel j = preserveRow P (count.relabel j) := by
  rw [formulaRelabelAsSubst]
  change (preserveRow P count).subst (fun a => emb (.var (j a))) = _
  rw [preserveRowSubst]
  simp only [← termRelabelAsSubst]

theorem preserveBodyWitness (P : Program 2) (count state out parameter : OTerm α) :
    (preserveBody P count).subst
      (Sum.elim Term.var (fun i => emb (![state,out,parameter] i))) =
      (graph1 InternalUnpair.left parameter state ⊓
        InternalNumericIteration.repeatGraph (carryP P) out count state).imp
        (graph1 InternalUnpair.left parameter out) := by
  have he : (Sum.elim Term.var (fun i => emb (![state,out,parameter] i))) =
      (fun a => emb (Sum.elim Term.var ![state,out,parameter] a)) := by
    funext a
    cases a <;> rfl
  unfold preserveBody graph1
  rw [he,impSubst,conjunctionSubst]
  simp only [programSubst,repeatSubst,consTermSubst,witnessLift,Term.subst,Sum.elim_inr,emptySubst]
  rfl

theorem preserveInstantiate (P : Program 2) (count : OTerm (α ⊕ Fin 1)) (t : OTerm α) :
    instantiate (preserveRow P count) (emb t) = preserveRow P (count.subst (bindTerm t)) := by
  rw [instantiate,bindEmbedding,preserveRowSubst]
theorem preserveSuccessor (P : Program 2) (count : OTerm (α ⊕ Fin 1)) :
    successorInstance (preserveRow P count) = preserveRow P (count.subst nextTerm) := by
  rw [successorInstance,nextEmbedding,preserveRowSubst]

theorem rowApply (P : Program 2) (out count state parameter : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (preserveRow P count)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter state)))
    (hr : Nonempty (Derivation body Gamma (InternalNumericIteration.repeatGraph (carryP P) out count state))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter out)) := by
  have h := actualFiniteUniversalElimination body α 3 Gamma (preserveBody P count)
    (fun i => emb (![state,out,parameter] i)) hrow
  rw [preserveBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hl⟩ := hl
  obtain ⟨hr⟩ := hr
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hl hr)⟩

theorem zeroCore (P : Program 2) (out state parameter : OTerm α)
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter state)))
    (hr : Nonempty (Derivation body Gamma (InternalNumericIteration.repeatGraph (carryP P) out z state))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter out)) := by
  obtain ⟨he⟩ := repeatZeroRecover (carryP P) out state hr
  exact headTransport InternalUnpair.left parameter state out Fin.elim0 ⟨symm he⟩ hl

theorem zeroRow (P : Program 2) : Nonempty (Derivation body Gamma (preserveRow P z)) := by
  unfold preserveRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let state : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let parameter : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let A := graph1 InternalUnpair.left parameter state ⊓
    InternalNumericIteration.repeatGraph (carryP P) out z state
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) P out state parameter
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [preserveBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem succCore (P : Program 2) (out count state parameter : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (preserveRow P count)))
    (hl : Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter state)))
    (hr : Nonempty (Derivation body Gamma (InternalNumericIteration.repeatGraph (carryP P) out (suc count) state))) :
    Nonempty (Derivation body Gamma (graph1 InternalUnpair.left parameter out)) := by
  apply programCases (InternalNumericIteration.repeatProgram (carryP P))
    (Fin.cons count (Fin.cons state Fin.elim0)) _
  intro β j Delta result hj ht
  rw [graph1Rename]
  simp only [consTermRename,emptyRename] at ht
  have hrow' := renameInto hrow j Delta hj
  rw [preserveRowRename] at hrow'
  have hl' := renameInto hl j Delta hj
  rw [graph1Rename] at hl'
  have hr' := renameInto hr j Delta hj
  simp only [repeatRename,sucRelabel] at hr'
  exact carryPreserve P (out.relabel j) result (parameter.relabel j)
    (rowApply P result (count.relabel j) (state.relabel j) (parameter.relabel j) hrow' hl' ht)
    (repeatSuccRecover (carryP P) (count.relabel j) result (out.relabel j) (state.relabel j) ht hr')

theorem succRow (P : Program 2) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (preserveRow P count))) :
    Nonempty (Derivation body Gamma (preserveRow P (suc count))) := by
  unfold preserveRow
  apply actualFiniteUniversalIntroduction body α 3 Gamma
  let state : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let parameter : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let c := count.relabel (Sum.inl : α → α ⊕ Fin 3)
  let A := graph1 InternalUnpair.left parameter state ⊓
    InternalNumericIteration.repeatGraph (carryP P) out (suc c) state
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [preserveRowRename] at hrow'
  obtain ⟨d⟩ := succCore P out c state parameter hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [preserveBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem allRows (P : Program 2) (count : OTerm α) :
    Nonempty (Derivation body Gamma (preserveRow P count)) := by
  let theta : Formula (α ⊕ Fin 1) := preserveRow P (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,preserveInstantiate,varBind] using (zeroRow (body := body) (Gamma := Gamma) P)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      P (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,preserveSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,preserveInstantiate,varBind] using (Nonempty.intro h)

theorem preserveParameter (P : Program 2) (out count state parameter : OTerm α)
    (hl : Nonempty (Derivation body Gamma (programGraph InternalUnpair.left parameter (Fin.cons state Fin.elim0))))
    (hr : Nonempty (Derivation body Gamma (InternalNumericIteration.repeatGraph (carryP P) out count state))) :
    Nonempty (Derivation body Gamma (programGraph InternalUnpair.left parameter (Fin.cons out Fin.elim0))) :=
  rowApply P out count state parameter (allRows P count) hl hr

theorem actualOriginalParameterizedNumericIterationParameterPreservation :
    InternalParameterizedNumericIterationTargets.ActualOriginalParameterizedNumericIterationParameterPreservation := by
  intro body P α Gamma out count state parameter
  let A := programGraph InternalUnpair.left parameter (Fin.cons state Fin.elim0) ⊓
    InternalNumericIteration.repeatGraph (carryP P) out count state
  obtain ⟨d⟩ := preserveParameter (body := body) (Gamma := A :: Gamma) P out count state parameter
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  exact ⟨Derivation.implicationIntroduction d⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
