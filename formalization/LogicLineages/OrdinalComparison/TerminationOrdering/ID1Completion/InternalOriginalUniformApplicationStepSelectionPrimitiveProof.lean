module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStepPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaProgramsDecoderProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionPrimitiveProof
open Source InternalOriginalUniformApplicationStepSelection
open InternalOriginalUniformParameterLeaves (parameterObject)

attribute [local irreducible] Primrec

/-- Compose the original numeric step test with the original context and
Object decoders. All four raw inputs remain variable, and malformed contexts
retain the literal zero default of leafValue. -/
theorem leafValuePrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (leafValue n arity) := by
  have getP (i : Fin 4) : Primrec (fun v : List.Vector Nat 4 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hc := (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp
    (Primrec.fst.comp (Primrec.unpair.comp (getP 3)))
  have ho : Primrec (fun v : List.Vector Nat 4 => parameterObject (v.get 0) (v.get 3)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp
      (Primrec₂.natPair.comp (Primrec.snd.comp (Primrec.unpair.comp (getP 3))) (getP 0))
  let Input := (List.Vector Nat 4 × OrdinaryArithmeticQuotient.Context n) × ContextUniform.Object
  have hcontext : Primrec (fun p : Input => p.1.2) := Primrec.snd.comp Primrec.fst
  have hvector : Primrec (fun p : Input => p.1.1) := Primrec.fst.comp Primrec.fst
  have hGamma : Primrec (fun p : Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have hsource : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have htarget := (getP 1).comp hvector
  have hcertificate := (getP 2).comp hvector
  have hb : Primrec (fun p : Input =>
      (NumberedNumericStep.numericStepTest n arity p.1.2.1.1 p.1.2.1.2 p.2.1 p.1.2.2
        p.2.2 (p.1.1.get 1) (p.1.1.get 2)).toNat) :=
    (Primrec.dom_bool Bool.toNat).comp
      ((NumberedNumericStepPrimrecProof.numericStepPrimitive n arity).comp
        ((Primrec.fst.comp hcontext).pair
          ((Primrec.snd.comp hcontext).pair
            (hGamma.pair (hsource.pair (htarget.pair hcertificate))))))
  have hm := Primrec.option_map (ho.comp Primrec.fst) hb.to₂
  have hp := Primrec.option_getD.comp (Primrec.option_bind hc hm.to₂) (Primrec.const 0)
  apply hp.of_eq
  intro v
  cases hdecode : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n)
      (Nat.unpair (v.get 3)).1 <;>
    cases hobject : parameterObject (v.get 0) (v.get 3) <;>
    simp only [leafValue,hdecode,hobject,Option.bind_none,Option.bind_some,
      Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionPrimitiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformApplicationStepSelectionPrimitiveProof
