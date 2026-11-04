module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientCertificatesPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientDecoderProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientPrimitiveProof

open Source OrdinaryArithmeticQuotient OrdinaryArithmeticQuotientTargets
open NumberedNumericQuotientEdge NumberedQuotientPathCertificates

attribute [local irreducible] Primrec numericEdgeTest positivePathTest

theorem decodedCheckerPrimitive {n : Nat} (f : Context n → Nat → Nat → Nat → Bool)
    (hf : Primrec (fun p : Context n × Nat × Nat × Nat => f p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun v : List.Vector Nat 4 =>
      ((Encodable.decode (α := Context n) (v.get 0)).any
        (fun ctx => f ctx (v.get 1) (v.get 2) (v.get 3))).toNat) := by
  have getP (i : Fin 4) : Primrec (fun v : List.Vector Nat 4 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  have decodeP : Primrec (Encodable.decode : Nat → Option (Context n)) :=
    OrdinaryArithmeticQuotientDecoderProof.contextDecoderPrimitive n
  have hd : Primrec (fun v : List.Vector Nat 4 =>
      Encodable.decode (α := Context n) (v.get 0)) := decodeP.comp (getP 0)
  have hi : Primrec (fun p : List.Vector Nat 4 × Context n =>
      (p.2, p.1.get 1, p.1.get 2, p.1.get 3)) :=
    Primrec.snd.pair (((getP 1).comp Primrec.fst).pair
      (((getP 2).comp Primrec.fst).pair ((getP 3).comp Primrec.fst)))
  have hb : Primrec (fun p : List.Vector Nat 4 × Context n =>
      f p.2 (p.1.get 1) (p.1.get 2) (p.1.get 3)) := hf.comp hi
  have ho := NumberedQuotientPathPrimrecSupportProof.optionAnyPrimitive hd hb.to₂
  exact (Primrec.dom_bool Bool.toNat).comp ho

theorem encodedCheckersPrimitive : EncodedCheckersPrimitive := by
  intro n arity Gamma
  have hi : Primrec (fun p : Context n × Nat × Nat × Nat =>
      (p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)
  constructor
  · exact decodedCheckerPrimitive
      (fun ctx x y c => numericEdgeTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y c)
      ((NumberedQuotientCertificatesPrimrecProof.numericEdgePrimitive n arity Gamma).comp hi)
  · exact decodedCheckerPrimitive
      (fun ctx x y c => positivePathTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y c)
      ((NumberedQuotientCertificatesPrimrecProof.positivePathTestPrimitive n arity Gamma).comp hi)

theorem actualCheckerCalibration : ActualCheckerCalibration := by
  intro n arity Gamma symbols S table x y c
  simp [edgeValue, positiveValue, contextCode]

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientPrimitiveProof
