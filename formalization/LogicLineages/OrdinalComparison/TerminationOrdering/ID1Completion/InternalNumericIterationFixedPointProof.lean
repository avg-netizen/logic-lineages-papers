module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalNumericIteration InternalNumericIterationSyntaxProof InternalNumericIterationSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalRecursionGraphStepSyntaxProof SourceComputabilityFormulaSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- PA induction in the original calculus, retaining the actual fixed-point
graph in the context. The count is never replaced by a standard numeral. -/
theorem fixedValue (transition : Program 1) (count fixed : OTerm α)
    (hf : Nonempty (Derivation body Gamma
      (programGraph transition fixed (Fin.cons fixed Fin.elim0)))) :
    Nonempty (Derivation body Gamma (repeatGraph transition fixed count fixed)) := by
  let f := fixed.relabel (Sum.inl : α → α ⊕ Fin 1)
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (α ⊕ Fin 1) := repeatGraph transition f k f
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,f,k,instantiate,bindEmbedding,repeatSubst,liftBind,varBind] using
      (repeatZeroValue (body := body) (Gamma := Gamma) transition fixed)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have hf' := renameInto hf Sum.inl (theta :: Gamma.map weaken)
      (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    simp only [programRename,consTermRename,emptyRename] at hf'
    have h := repeatSuccValue (body := body) (Gamma := theta :: Gamma.map weaken)
      transition k f f f ⟨Derivation.hypothesis List.mem_cons_self⟩ hf'
    simpa only [theta,f,k,successorInstance,nextEmbedding,repeatSubst,nextLift,
      nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,f,k,instantiate,bindEmbedding,repeatSubst,liftBind,varBind] using
    (Nonempty.intro h)

theorem actualOriginalNumericIterationFixedPoint :
    InternalNumericIterationTargets.ActualOriginalNumericIterationFixedPoint := by
  intro body transition α out count fixed
  let A := programGraph transition fixed (Fin.cons fixed Fin.elim0)
  let P := repeatGraph transition out count fixed
  let Q := equal out fixed
  have forward : Nonempty (Derivation body [P,A] Q) := by
    change Nonempty (Derivation body [P,A] (equal out fixed))
    rw [equalEqn]
    exact valueUnique (repeatProgram transition) out fixed
      (Fin.cons count (Fin.cons fixed Fin.elim0))
      ⟨Derivation.hypothesis List.mem_cons_self⟩
      (fixedValue transition count fixed
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
  have backward : Nonempty (Derivation body [Q,A] P) := by
    have he : Derivation body [Q,A] (eqn out fixed) := by
      rw [← equalEqn]
      exact Derivation.hypothesis List.mem_cons_self
    exact outputTransport (repeatProgram transition) fixed out
      (Fin.cons count (Fin.cons fixed Fin.elim0)) ⟨symm he⟩
      (fixedValue transition count fixed
        ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩)
  obtain ⟨forward⟩ := forward
  obtain ⟨backward⟩ := backward
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction backward))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalNumericIterationFixedPointProof
