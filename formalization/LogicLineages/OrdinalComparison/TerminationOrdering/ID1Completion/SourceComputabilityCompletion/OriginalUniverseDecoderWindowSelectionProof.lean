module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHeadWindowPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderWindowSelectionProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedNumericDecoding
open NumberedFiniteUniverse OriginalUniverseDecoder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

attribute [local irreducible] Primrec

/-- The compiled leaf inspects one decoded head and one ORIGINAL Context.
In particular the context decoder is not replaced by Primrec.decode. -/
theorem headWindowPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : Nat × Nat => headWindowValue n arity p.1 p.2) := by
  let Input := Nat × Nat
  have hh : Primrec (fun p : Input => decodeHeadNumber n p.1) :=
    (NumberedHeadCodecPrimrecProof.headDecoderPrimitive n).comp Primrec.fst
  have hc : Primrec (fun p : Input =>
      Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) p.2) :=
    (OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n).comp Primrec.snd
  have hb : Primrec (fun p : (Input × HeadCode (Fin n)) × OrdinaryArithmeticQuotient.Context n =>
      (decide (HeadInWindow arity p.2.1.1 p.2.1.2 (decodeHead p.1.2))).toNat) :=
    (Primrec.dom_bool Bool.toNat).comp
      ((NumberedHeadWindowPrimrecProof.headWindowPrimitive n arity).comp
        ((Primrec.fst.comp (Primrec.fst.comp Primrec.snd)).pair
          ((Primrec.snd.comp (Primrec.fst.comp Primrec.snd)).pair
            (Primrec.snd.comp Primrec.fst))))
  have hm := Primrec.option_map (hc.comp Primrec.fst) hb.to₂
  have hp := Primrec.option_getD.comp (Primrec.option_bind hh hm.to₂) (Primrec.const 0)
  apply hp.of_eq
  intro p
  cases hh : decodeHeadNumber n p.1 <;>
    cases hc : Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) p.2 <;>
      simp only [headWindowValue,hh,hc,Option.bind_none,Option.bind_some,
        Option.map_none,Option.map_some,Option.getD_none,Option.getD_some]

theorem windowVectorPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun v : List.Vector Nat 2 => headWindowValue n arity (v.get 0) (v.get 1)) :=
  (headWindowPrimitive n arity).comp
    ((Primrec.vector_get.comp Primrec.id (Primrec.const 0)).pair
      (Primrec.vector_get.comp Primrec.id (Primrec.const 1)))

theorem actualOriginalUniverseWindowSelection :
    OriginalUniverseDecoderTargets.ActualOriginalUniverseWindowSelection := by
  intro n arity
  exact Proof.allPrimitiveFunctions 2 _ (windowVectorPrimitive n arity)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderWindowSelectionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderWindowSelectionProof
