module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaApplicationDecoderProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderPrimitiveProof
open Source ApplicationResultBuilder

attribute [local irreducible] Primrec

theorem resultOptionPrimitive (n : Nat) (arity : Fin n → Nat) : Primrec (resultOption n arity) := by
  let Inner := (List.Vector Nat 5 × ContextUniform.Object) × ContextUniform.Object
  have getP (i : Fin 5) : Primrec (fun v : List.Vector Nat 5 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have hv : Primrec (fun p : Inner => p.1.1) := Primrec.fst.comp Primrec.fst
  have hf : Primrec (fun p : Inner => p.1.2) := Primrec.snd.comp Primrec.fst
  have ha : Primrec (fun p : Inner => p.2) := Primrec.snd
  have hg := Primrec.fst.comp hf
  have happ := (JointGammaApplicationDecoderProof.decodedPrimitive n arity).comp
    (hg.pair (((getP 0).comp hv).pair (((getP 1).comp hv).pair
      (((getP 2).comp hv).pair ((Primrec.snd.comp hf).pair (Primrec.snd.comp ha))))))
  have he : Primrec (fun p : Inner × Nat => ContextUniform.objectCode p.1.1.2.1 p.2) :=
    Primrec.encode.comp ((hg.comp Primrec.fst).pair Primrec.snd)
  have hout := Primrec.option_map happ he.to₂
  have hguard : PrimrecPred (fun p : Inner => p.1.2.1 = p.2.1) :=
    Primrec.eq.comp hg (Primrec.fst.comp ha)
  have hi := Primrec.ite hguard hout (Primrec.const (none : Option Nat))
  have hdArgument : Primrec (fun p : List.Vector Nat 5 × ContextUniform.Object =>
      Encodable.decode (α := ContextUniform.Object) (p.1.get 4)) :=
    JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp ((getP 4).comp Primrec.fst)
  have hm := Primrec.option_bind hdArgument hi.to₂
  have hdFunction := JointGammaProgramsDecoderProof.objectDecoderPrimitive.comp (getP 3)
  exact (Primrec.option_bind hdFunction hm.to₂).of_eq (by intro v; rfl)

theorem actualPrimitive : ApplicationResultBuilderTargets.ActualPrimitive := by
  intro n arity
  have ho := resultOptionPrimitive n arity
  exact ⟨ho,Primrec.option_getD.comp ho (Primrec.const 0),
    (Primrec.dom_bool Bool.toNat).comp (Primrec.option_isSome.comp ho)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderPrimitiveProof
