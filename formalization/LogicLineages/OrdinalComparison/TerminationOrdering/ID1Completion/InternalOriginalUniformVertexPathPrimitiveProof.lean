module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesCodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathPrimitiveProof
open Source InternalOriginalUniformVertexPath InternalOriginalUniformVertexPathTargets
open InternalOriginalUniformParameterLeaves (parameterCode parameterObject)
open InternalOriginalUniformParameterLeavesCodecProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

/-- Only the original Object decoder and original vertex function are used.
The signature is fixed before all five natural coordinates. -/
theorem oldVertexPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (oldVertexValue n arity) := by
  have getP (i : Fin 5) : Primrec (fun v : List.Vector Nat 5 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have ho : Primrec (fun v : List.Vector Nat 5 => parameterObject (v.get 4) (v.get 0)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp
      (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp (getP 0))) (getP 4))
  let Input := List.Vector Nat 5 × ContextUniform.Object
  have hg : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have hx : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : Input => (Nat.unpair (p.1.get 0)).1) :=
    Primrec.fst.comp (Primrec.unpair.comp ((getP 0).comp Primrec.fst))
  have hp : Primrec (fun p : Input =>
      ((p.2.1,(Nat.unpair (p.1.get 0)).1,p.1.get 1,p.1.get 2,p.1.get 3),p.2.2)) :=
    (hg.pair (hc.pair (((getP 1).comp Primrec.fst).pair
      (((getP 2).comp Primrec.fst).pair ((getP 3).comp Primrec.fst))))).pair hx
  have hv := (ApplicationCertificateLiftPathPrimitiveProof.vertexPrimitive n arity).comp hp
  exact (Primrec.option_getD.comp (Primrec.option_map ho hv.to₂) (Primrec.const 0)).of_eq
    (by intro v; rfl)

/-- The original encoded parameter supplies precisely Gamma and context.
All remaining raw numeric inputs are unrestricted. -/
theorem oldVertexCalibrationAt (n : Nat) (arity : Fin n → Nat) (oldVertex : Program 5)
    (hc : OldVertexCalibrated n arity oldVertex)
    (symbols : List (Fin n)) (S Gamma : List Ty) (table : Fin n → Fin n → Bool) :
    VertexCalibratedAt n arity symbols S Gamma table oldVertex := by
  intro d e a x
  rw [hc]
  obtain ⟨_,ho⟩ := actualOriginalUniformParameterCodec.1 n symbols S Gamma table x
  change ((parameterObject x (parameterCode symbols S Gamma table)).map (fun obj =>
    ApplicationCertificateLiftPath.vertex n arity obj.1
      (Nat.unpair (parameterCode symbols S Gamma table)).1 d e a obj.2)).getD 0 = _
  rw [ho]
  simp only [parameterCode,Nat.unpair_pair,Option.map_some,Option.getD_some]

theorem actualOriginalUniformVertexProgram : ActualOriginalUniformVertexProgram := by
  intro n arity
  obtain ⟨oldVertex,hc⟩ := Proof.allPrimitiveFunctions 5 _ (oldVertexPrimitive n arity)
  exact ⟨oldVertex,hc,fun symbols S Gamma table =>
    oldVertexCalibrationAt n arity oldVertex hc symbols S Gamma table⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathPrimitiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathPrimitiveProof
