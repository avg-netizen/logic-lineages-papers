module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFixedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalUniverseDecoderInternalFuelNumericSyntaxProof OriginalUniverseDecoderInternalFuelNumericSupportProof

variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

/-- Fresh arithmetic induction on the literal direct recursion, at fixed c. -/
theorem fixedValue (transition : Program 2) (count fixed c : OTerm alpha)
    (hf : Nonempty (Derivation body Gamma (graph2 transition fixed fixed c))) :
    Nonempty (Derivation body Gamma (repeatGraph transition fixed count fixed c)) := by
  let f := fixed.relabel (Sum.inl : alpha → alpha ⊕ Fin 1)
  let parameter := c.relabel (Sum.inl : alpha → alpha ⊕ Fin 1)
  let k : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let theta : Formula (alpha ⊕ Fin 1) := repeatGraph transition f k f parameter
  have hz : Nonempty (Derivation body Gamma (instantiate theta (emb z))) := by
    simpa only [theta,f,parameter,k,instantiate,bindEmbedding,repeatSubst,liftBind,varBind] using
      (repeatZeroValue (body := body) (Gamma := Gamma) transition fixed c)
  have hs : Nonempty (Derivation body (theta :: Gamma.map weaken) (successorInstance theta)) := by
    have hf' := renameInto hf Sum.inl (theta :: Gamma.map weaken)
      (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
    rw [graph2Rename] at hf'
    have h := repeatSuccValue (body := body) (Gamma := theta :: Gamma.map weaken)
      transition k f f f parameter ⟨Derivation.hypothesis List.mem_cons_self⟩ hf'
    simpa only [theta,f,parameter,k,successorInstance,nextEmbedding,repeatSubst,nextLift,
      nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,f,parameter,k,instantiate,bindEmbedding,repeatSubst,liftBind,varBind] using
    (Nonempty.intro h)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFixedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelNumericFixedProof
