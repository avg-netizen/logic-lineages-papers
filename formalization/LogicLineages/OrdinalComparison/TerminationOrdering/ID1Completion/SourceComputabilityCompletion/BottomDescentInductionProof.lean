module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open SourceComputabilityCompletion.BottomRepresentative SourceComputabilityCompletion.BottomDescent
open SourceComputabilityCompletion.BottomDescentSyntaxProof SourceComputabilityCompletion.BottomDescentStepProof
open InternalOriginalUniformDescentSelection (Data)
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

theorem rowApply (data : Data) (window : Program 1) (count input out parameter indicator : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow data window count)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data window) out count input parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomGraph indicator input))) :
    Nonempty (Derivation body Gamma (bottomGraph indicator out)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (iterationBody data window count)
    (fun i => emb (![input,out,parameter,indicator] i)) hrow
  rw [bodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hr⟩ := hr
  obtain ⟨ha⟩ := ha
  obtain ⟨hb⟩ := hb
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hr
    (Derivation.conjunctionIntroduction ha hb))⟩

theorem zeroCore (data : Data) (window : Program 1) (input out parameter indicator : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data window) out z input parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomGraph indicator input))) :
    Nonempty (Derivation body Gamma (bottomGraph indicator out)) := by
  obtain ⟨he⟩ := valueUnique (InternalParameterizedNumericIteration.repeatP (step data window))
    out input (Fin.cons z (Fin.cons input (Fin.cons parameter Fin.elim0))) hr
    (InternalParameterizedNumericIterationLawsProof.zeroValue (step data window) input parameter)
  exact headTransport bottomTest indicator input out Fin.elim0 ⟨symm he⟩ hb

theorem zeroRow (data : Data) (window : Program 1) :
    Nonempty (Derivation body Gamma (iterationRow data window (z : OTerm α))) := by
  unfold BottomDescent.iterationRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let input : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let parameter : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let indicator : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := repeatGraph (step data window) out z input parameter ⊓
    (activeGraph data window input parameter ⊓ bottomGraph indicator input)
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) data window input out parameter indicator
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [BottomDescent.iterationBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem succCore (data : Data) (window : Program 1) (count input out parameter indicator : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow data window count)))
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data window) out (suc count) input parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomGraph indicator input))) :
    Nonempty (Derivation body Gamma (bottomGraph indicator out)) := by
  apply programCases (step data window) (Fin.cons input (Fin.cons parameter Fin.elim0)) _
  intro β j Delta next hj ht
  rw [bottomRename]
  have ht' : Nonempty (Derivation body Delta
      (graph2 (step data window) next (input.relabel j) (parameter.relabel j))) := by
    simpa only [graph2,consTermRename,emptyRename] using ht
  have hrow' := renameInto hrow j Delta hj
  rw [rowRename] at hrow'
  have hr' := renameInto hr j Delta hj
  simp only [parameterRepeatRename,sucRelabel] at hr'
  have ha' := renameInto ha j Delta hj
  rw [activeRename] at ha'
  have hb' := renameInto hb j Delta hj
  rw [bottomRename] at hb'
  have hn := activeNext data window next (input.relabel j) (parameter.relabel j) ha' ht'
  have hbnext := forwardStep data window next (input.relabel j) (parameter.relabel j)
    (indicator.relabel j) ha' hb' ht'
  have htail := frontSuccForward (step data window) (out.relabel j) (count.relabel j)
    (input.relabel j) next (parameter.relabel j) ht' hr'
  exact rowApply data window (count.relabel j) next (out.relabel j) (parameter.relabel j)
    (indicator.relabel j) hrow' htail hn hbnext

theorem succRow (data : Data) (window : Program 1) (count : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (iterationRow data window count))) :
    Nonempty (Derivation body Gamma (iterationRow data window (suc count))) := by
  unfold BottomDescent.iterationRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let input : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let parameter : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let indicator : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let c := count.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := repeatGraph (step data window) out (suc c) input parameter ⊓
    (activeGraph data window input parameter ⊓ bottomGraph indicator input)
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨d⟩ := succCore data window c input out parameter indicator hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self))⟩
  simpa only [BottomDescent.iterationBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Induction takes place inside the original full-language calculus.
Neither a metalanguage iterate induction nor a reflected truth is used. -/
theorem allRows (data : Data) (window : Program 1) (count : OTerm α) :
    Nonempty (Derivation body Gamma (iterationRow data window count)) := by
  let theta : Formula (α ⊕ Fin 1) := iterationRow data window (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,BottomDescentSyntaxProof.rowInstantiate,varBind] using
      (zeroRow (body := body) (Gamma := Gamma) data window)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      data window (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,BottomDescentSyntaxProof.rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,BottomDescentSyntaxProof.rowInstantiate,varBind] using (Nonempty.intro h)

theorem repeatForward (data : Data) (window : Program 1) (count input out parameter indicator : OTerm α)
    (hr : Nonempty (Derivation body Gamma (repeatGraph (step data window) out count input parameter)))
    (ha : Nonempty (Derivation body Gamma (activeGraph data window input parameter)))
    (hb : Nonempty (Derivation body Gamma (bottomGraph indicator input))) :
    Nonempty (Derivation body Gamma (bottomGraph indicator out)) :=
  rowApply data window count input out parameter indicator (allRows data window count) hr ha hb

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomDescentInductionProof
