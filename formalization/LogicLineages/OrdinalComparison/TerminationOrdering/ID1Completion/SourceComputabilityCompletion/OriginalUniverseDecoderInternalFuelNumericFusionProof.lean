module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFusionSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFusionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalOriginalOrderSyntaxProof
open OriginalUniverseDecoderInternalFuelNumericSyntaxProof OriginalUniverseDecoderInternalFuelNumericSupportProof OriginalUniverseDecoderInternalFuelNumericFusionSyntaxProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem rowApply (transition : Program 2) (second first initial intermediate out c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fusionRow transition second)))
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial c)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out second intermediate c))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial c)) := by
  have h := actualFiniteUniversalElimination body α 5 Gamma (fusionBody transition second)
    (fun i => emb (![first,initial,intermediate,out,c] i)) hrow
  rw [fusionBodyWitness] at h
  obtain ⟨h⟩ := h
  obtain ⟨hm⟩ := hm
  obtain ⟨ho⟩ := ho
  exact ⟨Derivation.implicationElimination h (Derivation.conjunctionIntroduction hm ho)⟩

theorem zeroCore (transition : Program 2) (first initial intermediate out c : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial c)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out z intermediate c))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first z) initial c)) := by
  obtain ⟨he⟩ := repeatZeroRecover transition out intermediate c ho
  have h := outputTransport (repeatProgram transition) intermediate out
    ![first,initial,c] ⟨symm he⟩ hm
  exact headTransport (repeatProgram transition) out first (OrdinaryArithmetic.addTerm first z)
    ![initial,c] ⟨symm (addZero first)⟩ h

theorem zeroRow (transition : Program 2) :
    Nonempty (Derivation body Gamma (fusionRow transition z)) := by
  unfold fusionRow
  apply actualFiniteUniversalIntroduction body α 5 Gamma
  let first : OTerm (α ⊕ Fin 5) := .var (.inr 0)
  let initial : OTerm (α ⊕ Fin 5) := .var (.inr 1)
  let intermediate : OTerm (α ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 5) := .var (.inr 3)
  let c : OTerm (α ⊕ Fin 5) := .var (.inr 4)
  let A := repeatGraph transition intermediate first initial c ⊓
    repeatGraph transition out z intermediate c
  obtain ⟨d⟩ := zeroCore (body := body)
    (Gamma := A :: Gamma.map (fun p => p.relabel Sum.inl)) transition first initial intermediate out c
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [fusionBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

theorem succCore (transition : Program 2) (second first initial intermediate out c : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fusionRow transition second)))
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial c)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out (suc second) intermediate c))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first (suc second)) initial c)) := by
  apply programCases (repeatProgram transition) (Fin.cons second (Fin.cons intermediate (Fin.cons c Fin.elim0))) _
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
    (out.relabel j) (intermediate.relabel j) (c.relabel j) hr ho'
  have hfirst := rowApply transition (second.relabel j) (first.relabel j) (initial.relabel j)
    (intermediate.relabel j) result (c.relabel j) hrow' hm' hr
  have hnext := repeatSuccValue transition
    (OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j)) result
    (out.relabel j) (initial.relabel j) (c.relabel j) hfirst ht
  exact headTransport (repeatProgram transition) (out.relabel j)
    (suc (OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j)))
    (OrdinaryArithmetic.addTerm (first.relabel j) (suc (second.relabel j)))
    ![initial.relabel j,c.relabel j]
    ⟨symm (addSucc (first.relabel j) (second.relabel j))⟩ hnext

theorem succRow (transition : Program 2) (second : OTerm α)
    (hrow : Nonempty (Derivation body Gamma (fusionRow transition second))) :
    Nonempty (Derivation body Gamma (fusionRow transition (suc second))) := by
  unfold fusionRow
  apply actualFiniteUniversalIntroduction body α 5 Gamma
  let first : OTerm (α ⊕ Fin 5) := .var (.inr 0)
  let initial : OTerm (α ⊕ Fin 5) := .var (.inr 1)
  let intermediate : OTerm (α ⊕ Fin 5) := .var (.inr 2)
  let out : OTerm (α ⊕ Fin 5) := .var (.inr 3)
  let c : OTerm (α ⊕ Fin 5) := .var (.inr 4)
  let n := second.relabel (Sum.inl : α → α ⊕ Fin 5)
  let A := repeatGraph transition intermediate first initial c ⊓
    repeatGraph transition out (suc n) intermediate c
  let Delta := A :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 5))
  have hrow' := renameInto hrow Sum.inl Delta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [fusionRowRename] at hrow'
  obtain ⟨d⟩ := succCore transition n first initial intermediate out c hrow'
    ⟨Derivation.conjunctionLeft (Derivation.hypothesis List.mem_cons_self)⟩
    ⟨Derivation.conjunctionRight (Derivation.hypothesis List.mem_cons_self)⟩
  simpa only [fusionBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))

/-- Induction in the SECOND original arithmetic count. The only addition
identities used are the existing PA zero and successor axioms. -/
theorem allRows (transition : Program 2) (second : OTerm α) :
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

theorem fusionValue (transition : Program 2) (first second initial intermediate out c : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial c)))
    (ho : Nonempty (Derivation body Gamma (repeatGraph transition out second intermediate c))) :
    Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial c)) :=
  rowApply transition second first initial intermediate out c (allRows transition second) hm ho

theorem fusionRecover (transition : Program 2) (first second initial intermediate out c : OTerm α)
    (hm : Nonempty (Derivation body Gamma (repeatGraph transition intermediate first initial c)))
    (ho : Nonempty (Derivation body Gamma
      (repeatGraph transition out (OrdinaryArithmetic.addTerm first second) initial c))) :
    Nonempty (Derivation body Gamma (repeatGraph transition out second intermediate c)) := by
  apply programCases (repeatProgram transition) (Fin.cons second (Fin.cons intermediate (Fin.cons c Fin.elim0))) _
  intro β j Delta result hj hr
  rw [repeatRename]
  simp only [consTermRename,emptyRename] at hr
  have hm' := renameInto hm j Delta hj
  rw [repeatRename] at hm'
  have ho' := renameInto ho j Delta hj
  simp only [repeatRename,addRelabel] at ho'
  have hsum := fusionValue transition (first.relabel j) (second.relabel j) (initial.relabel j)
    (intermediate.relabel j) result (c.relabel j) hm' hr
  have he := valueUnique (repeatProgram transition) result (out.relabel j)
    ![OrdinaryArithmetic.addTerm (first.relabel j) (second.relabel j),initial.relabel j,c.relabel j] hsum ho'
  exact outputTransport (repeatProgram transition) result (out.relabel j)
    ![second.relabel j,intermediate.relabel j,c.relabel j] he hr


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFusionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFusionProof
