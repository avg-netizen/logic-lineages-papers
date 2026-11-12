module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.OriginalStructuralKeyIteration
open SourceComputabilityCompletion.OriginalStructuralKeyIterationSyntaxProof SourceComputabilityCompletion.OriginalStructuralKeyIterationStepProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof
open InternalParameterizedNumericIteration InternalParameterizedNumericIterationSyntaxProof
open InternalParameterizedNumericIterationLawsProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalBetaTotalityProof InternalPositiveUnfoldingSupportProof
open InternalClosedPrograms InternalClosedProgramsBindingProof SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (data : Data) (count input out parameter indicator : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow data count)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data) out count input parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hb : Nonempty (Derivation body Gamma (markGraph data indicator input parameter))) :
    Nonempty (Derivation body Gamma (markGraph data indicator out parameter)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (iterationBody data count)
    (fun i => emb (![input,out,parameter,indicator] i)) hrow
  rw [bodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hr⟩ := hr
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hr
    (Derivation.conjunctionIntroduction ha hb))⟩

theorem zeroCore (data : Data) (input out parameter indicator : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data) out z input parameter)))
    (hb : Nonempty (Derivation body Gamma (markGraph data indicator input parameter))) :
    Nonempty (Derivation body Gamma (markGraph data indicator out parameter)) := by
  obtain ⟨he⟩ := valueUnique (InternalParameterizedNumericIteration.repeatP (step data))
    out input (Fin.cons z (Fin.cons input (Fin.cons parameter Fin.elim0))) hr
    (InternalParameterizedNumericIterationLawsProof.zeroValue (step data) input parameter)
  exact headTransport data.observer indicator input out (Fin.cons parameter Fin.elim0) ⟨symm he⟩ hb

theorem zeroRow (data : Data) :
    Nonempty (Derivation body Gamma (iterationRow data (z : OTerm α))) := by
  unfold OriginalStructuralKeyIteration.iterationRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let input : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let parameter : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let indicator : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := repeatGraph (step data) out z input parameter ⊓
    (activeGraph data input parameter ⊓ markGraph data indicator input parameter)
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) data input out parameter indicator
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [iterationBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem succCore (data : Data) (closure : Closure data) (supply : Preservation data) (count input out parameter indicator : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow data count)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data) out (suc count) input parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hb : Nonempty (Derivation body Gamma (markGraph data indicator input parameter))) :
    Nonempty (Derivation body Gamma (markGraph data indicator out parameter)) := by
  apply programCases (step data) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta next hj ht
  rw [markRename]
  have ht' : Nonempty (Derivation body Delta
      (graph2 (step data) next (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using ht
  have hrow' := renameInto hrow j Delta hj
  rw [rowRename] at hrow'
  have hr' := renameInto hr j Delta hj
  simp only [parameterRepeatRename,sucRelabel] at hr'
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hb' := renameInto hb j Delta hj
  rw [markRename] at hb'
  have hn := closure body β Delta next (input.relabel j) (parameter.relabel j) ha' ht'
  have hbnext := forwardStep data supply next (input.relabel j) (parameter.relabel j)
    (indicator.relabel j) ha' hb' ht'
  have htail := frontSuccForward (step data) (out.relabel j) (count.relabel j)
    (input.relabel j) next (parameter.relabel j) ht' hr'
  exact rowApply data (count.relabel j) next (out.relabel j) (parameter.relabel j)
    (indicator.relabel j) hrow' htail hn hbnext

theorem succRow (data : Data) (closure : Closure data) (supply : Preservation data) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow data count))) :
    Nonempty (Derivation body Gamma (iterationRow data (suc count))) := by
  unfold OriginalStructuralKeyIteration.iterationRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let input : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let parameter : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let indicator : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let c := count.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := repeatGraph (step data) out (suc c) input parameter ⊓
    (activeGraph data input parameter ⊓ markGraph data indicator input parameter)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨d⟩ := succCore data closure supply c input out parameter indicator hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [iterationBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Induction takes place inside the original full-language calculus.
Neither a metalanguage iterate induction nor a reflected truth is used. -/
theorem allRows (data : Data) (closure : Closure data) (supply : Preservation data) (count : OTerm α) :
    Nonempty (Derivation body Gamma (iterationRow data count)) := by
  let theta : Formula (α ⊕ Fin 1) := iterationRow data (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,OriginalStructuralKeyIterationSyntaxProof.rowInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) data)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      data closure supply (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,OriginalStructuralKeyIterationSyntaxProof.rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,OriginalStructuralKeyIterationSyntaxProof.rowInstantiate,varBind] using (Nonempty.intro h)

theorem repeatForward (data : Data) (closure : Closure data) (supply : Preservation data) (count input out parameter indicator : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data) out count input parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data input parameter)))
    (hb : Nonempty (Derivation body Gamma (markGraph data indicator input parameter))) :
    Nonempty (Derivation body Gamma (markGraph data indicator out parameter)) :=
  rowApply data count input out parameter indicator (allRows data closure supply count) hr ha hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralKeyIterationProof
