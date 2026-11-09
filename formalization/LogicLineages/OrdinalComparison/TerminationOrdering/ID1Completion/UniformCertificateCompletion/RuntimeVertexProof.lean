module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomRepresentativeEvaluationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexProof
open Source ContextUniform InternalOriginalUniformParameterLeaves
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec ApplicationCertificateLiftPath.vertex

theorem valuePrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (RuntimeVertex.value n arity) := by
  have getP (i : Fin 5) : Primrec (fun v : List.Vector Nat 5 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have ho : Primrec (fun v : List.Vector Nat 5 => parameterObject 0 (v.get 0)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp
      (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp (getP 0))) (Primrec.const 0))
  let Input := List.Vector Nat 5 × Object
  have getV (i : Fin 5) : Primrec (fun p : Input => p.1.get i) :=
    (getP i).comp Primrec.fst
  have hGamma : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have hcontext : Primrec (fun p : Input => (Nat.unpair (p.1.get 0)).1) :=
    Primrec.fst.comp (Primrec.unpair.comp (getV 0))
  have hb : Primrec (fun p : Input =>
      ApplicationCertificateLiftPath.vertex n arity p.2.1 (Nat.unpair (p.1.get 0)).1
        (p.1.get 1) (p.1.get 2) (p.1.get 3) (p.1.get 4)) :=
    (ApplicationCertificateLiftPathPrimitiveProof.vertexPrimitive n arity).comp
      ((hGamma.pair (hcontext.pair ((getV 1).pair ((getV 2).pair (getV 3))))).pair (getV 4))
  have hm := Primrec.option_map ho hb.to₂
  have hp := Primrec.option_getD.comp hm (Primrec.const 0)
  apply hp.of_eq
  intro v
  cases hd : parameterObject 0 (v.get 0) <;>
    simp only [RuntimeVertex.value,hd,Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

/-- Original primitive compilation selects one actual Program. Original
Object-code totality then exposes its runtime Gamma slice at EVERY p;
the original context remains the caller's raw left coordinate. -/
theorem actualGlobalRuntimeVertexSelection : RuntimeVertexTargets.ActualGlobalRuntimeVertexSelection := by
  intro n arity
  obtain ⟨vertex,hvertex⟩ := Proof.allPrimitiveFunctions 5 (RuntimeVertex.value n arity)
    (valuePrimitive n arity)
  refine ⟨vertex,hvertex,?_⟩
  intro parameter
  obtain ⟨Gamma,hGamma⟩ :=
    SourceComputabilityCompletion.BottomRepresentativeEvaluationProof.parameterGamma parameter
  refine ⟨Gamma,?_⟩
  intro domain codomain argument value
  rw [hvertex]
  change ((parameterObject 0 parameter).map (fun obj =>
    ApplicationCertificateLiftPath.vertex n arity obj.1 (Nat.unpair parameter).1
      domain codomain argument value)).getD 0 = _
  rw [hGamma 0]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertexProof
