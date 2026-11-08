module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration InternalNumericIterationSyntaxProof InternalNumericIterationSupportProof
open InternalNumericIterationFusionSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof InternalOriginalOrderSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (transition : Program 1) (second first initial intermediate out : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fusionRow transition second)))
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out second intermediate))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial)) := by
  have h := actualFiniteUniversalElimination body α 4 Gamma (fusionBody transition second)
    (fun i => emb (![first,initial,intermediate,out] i)) hrow
  rw [fusionBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hm⟩ := hm
  obtain ⟨ho⟩ := ho
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hm ho)⟩

theorem zeroCore (transition : Program 1) (first initial intermediate out : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out z intermediate))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first z) initial)) := by
  obtain ⟨he⟩ := repeatZeroRecover transition out intermediate ho
  have h := outputTransport (repeatProgram transition) intermediate out
    (Fin.cons first (Fin.cons initial Fin.elim0)) ⟨symm he⟩ hm
  exact headTransport (repeatProgram transition) out first (OrdinaryArithmetic.addTerm first z)
    (Fin.cons initial Fin.elim0) ⟨symm (addZero first)⟩ h

theorem zeroRow (transition : Program 1) :
    Nonempty (Derivation body Gamma (fusionRow transition z)) := by
  unfold fusionRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let first : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let initial : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let intermediate : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let A := repeatGraph transition intermediate first initial ⊓
    repeatGraph transition out z intermediate
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) transition first initial intermediate out
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [fusionBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem succCore (transition : Program 1) (second first initial intermediate out : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fusionRow transition second)))
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out (suc second) intermediate))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first (suc second)) initial)) := by
  apply programCases (repeatProgram transition) (Fin.cons second (Fin.cons intermediate Fin.elim0)) _
  intro β j Delta result hj hr
  simp only [repeatRename,addRelabel,sucRelabel]
  simp only [consTermRename,emptyRename] at hr
  have hrow' := renameInto hrow j Delta hj
  rw [fusionRowRename] at hrow'
  have hm' := renameInto hm j Delta hj
  rw [repeatRename] at hm'
  have ho' := renameInto ho j Delta hj
  simp only [repeatRename,sucRelabel] at ho'
  have ht := repeatSuccRecover transition (second.relabel j) result
    (out.relabel j) (intermediate.relabel j) hr ho'
  have hfirst := rowApply transition (second.relabel j) (first.relabel j) (initial.relabel j)
    (intermediate.relabel j) result hrow' hm' hr
  have hnext := repeatSuccValue transition
    (OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j)) result
    (out.relabel j) (initial.relabel j) hfirst ht
  exact headTransport (repeatProgram transition) (out.relabel j)
    (suc (OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j)))
    (OrdinaryArithmetic.addTerm (first.relabel j) (suc (second.relabel j)))
    (Fin.cons (initial.relabel j) Fin.elim0)
    ⟨symm (addSucc (first.relabel j) (second.relabel j))⟩ hnext

theorem succRow (transition : Program 1) (second : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fusionRow transition second))) :
    Nonempty (Derivation body Gamma (fusionRow transition (suc second))) := by
  unfold fusionRow
  apply actualFiniteUniversalIntroduction body α 4 Gamma
  let first : OTerm (α ⊕ Fin 4) := .var (.inr 0)
  let initial : OTerm (α ⊕ Fin 4) := .var (.inr 1)
  let intermediate : OTerm (α ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 4) := .var (.inr 3)
  let n := second.relabel (Sum.inl : α → α ⊕ Fin 4)
  let A := repeatGraph transition intermediate first initial ⊓
    repeatGraph transition out (suc n) intermediate
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [fusionRowRename] at hrow'
  obtain ⟨d⟩ := succCore transition n first initial intermediate out hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [fusionBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Induction in the SECOND original arithmetic count. The only addition
identities used are the existing PA zero and successor axioms. -/
theorem allRows (transition : Program 1) (second : OTerm α) :
    Nonempty (Derivation body Gamma (fusionRow transition second)) := by
  let theta : Formula (α ⊕ Fin 1) := fusionRow transition (.var (.inr 0))
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,fusionInstantiate,varBind] using (zeroRow (body := body) (Gamma := Gamma) transition)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Gamma := theta :: Gamma.map weaken)
      transition (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,fusionSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb second) (natInduction theta hz hs)
  simpa only [theta,fusionInstantiate,varBind] using (Nonempty.intro h)

theorem fusionValue (transition : Program 1) (first second initial intermediate out : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out second intermediate))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial)) :=
  rowApply transition second first initial intermediate out (allRows transition second) hm ho

theorem fusionRecover (transition : Program 1) (first second initial intermediate out : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial)))
    (ho : Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out second intermediate)) := by
  apply programCases (repeatProgram transition) (Fin.cons second (Fin.cons intermediate Fin.elim0)) _
  intro β j Delta result hj hr
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hm' := renameInto hm j Delta hj
  rw [repeatRename] at hm'
  have ho' := renameInto ho j Delta hj
  simp only [repeatRename,addRelabel] at ho'
  have hsum := fusionValue transition (first.relabel j) (second.relabel j) (initial.relabel j)
    (intermediate.relabel j) result hm' hr
  have he := valueUnique (repeatProgram transition) result (out.relabel j)
    (Fin.cons (OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j))
      (Fin.cons (initial.relabel j) Fin.elim0)) hsum ho'
  exact outputTransport (repeatProgram transition) result (out.relabel j)
    (Fin.cons (second.relabel j) (Fin.cons (intermediate.relabel j) Fin.elim0)) he hr

theorem actualOriginalNumericIterationAdditionFusion :
    InternalNumericIterationTargets.ActualOriginalNumericIterationAdditionFusion := by
  intro body transition α out first second initial intermediate
  let A := repeatGraph transition intermediate first initial
  let P := repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial
  let Q := repeatGraph transition out second intermediate
  have forward : Nonempty (Derivation body [P,A] Q) :=
    fusionRecover transition first second initial intermediate out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  have backward : Nonempty (Derivation body [Q,A] P) :=
    fusionValue transition first second initial intermediate out
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFusionProof
