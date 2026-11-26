module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRepeatSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalRawListRepeat InternalRawListRepeatSyntaxProof InternalRawListRepeatSupportProof
open InternalListCodec InternalListInduction InternalListInductionProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem fixedAtCode (transition : Program 1) (state code : OTerm α) :
    atCode (repeatGraph transition (state.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      (state.relabel Sum.inl)) code = repeatGraph transition state code state := by
  simp only [atCode,instantiate,bindEmbedding,repeatSubst,liftBind,varBind]

theorem fixedAtIndex (transition : Program 1) (state : OTerm α) (i : Fin 3) :
    atIndex (repeatGraph transition (state.relabel Sum.inl) (.var (.inr (0 : Fin 1)))
      (state.relabel Sum.inl)) i =
        repeatGraph transition (state.relabel Sum.inl) (.var (.inr i))
          (state.relabel Sum.inl) := by
  rw [atIndex,repeatRename]
  simp only [Term.relabel_relabel,Term.relabel]
  rfl

/-- The original full-language list-code induction retains the fixed graph
in the context. Its argument is an arbitrary raw code, not numerical fuel or
an externally decoded list. Every literal cons uses the same fixed state. -/
theorem fixedValue (transition : Program 1) (state code : OTerm α)
    (hf : Nonempty (Derivation body Gamma
      (programGraph transition state (Fin.cons state Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition state code state)) := by
  let theta : Formula (α ⊕ Fin 1) :=
    repeatGraph transition (state.relabel Sum.inl) (.var (.inr 0)) (state.relabel Sum.inl)
  have hz : Nonempty (Derivation body Gamma (atCode theta z)) := by
    rw [fixedAtCode]
    exact repeatZeroValue transition state
  have hs : Nonempty (Derivation body Gamma (constructors theta)) := by
    unfold constructors
    apply actualFiniteUniversalIntroduction body α 3 Gamma
    simp only [constructorBody,theta,fixedAtIndex]
    let c : OTerm (α ⊕ Fin 3) := .var (.inr 0)
    let h : OTerm (α ⊕ Fin 3) := .var (.inr 1)
    let t : OTerm (α ⊕ Fin 3) := .var (.inr 2)
    let f := state.relabel (Sum.inl : α → α ⊕ Fin 3)
    let C := InternalListCodecSupportProof.consGraph c h t
    let R := repeatGraph transition f t f
    let Delta := R :: C :: Gamma.map (fun p => p.relabel (Sum.inl : α → α ⊕ Fin 3))
    have hf' := InternalGraphCompositionFunctionalityProof.renameInto hf Sum.inl Delta
      (fun p hp => List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)))
    simp only [programRename,consTermRename,emptyRename] at hf'
    obtain ⟨d⟩ := repeatConsValue (body := body) (Gamma := Delta)
      transition c h t f f f
      ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
      ⟨Derivation.hypothesis List.mem_cons_self⟩ hf'
    exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := actualOriginalListInductionAtCode body α Gamma theta code
    ⟨Derivation.conjunctionIntroduction hz hs⟩
  rw [fixedAtCode] at h
  exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRepeatSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaRepeatSupportProof
