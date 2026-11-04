module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirectTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirectProof
open Source OrdinaryArithmetic OrdinaryArithmeticQuotient OrdinaryArithmeticDirect
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem encodedCheckerPrimitive : OrdinaryArithmeticDirectTargets.EncodedCheckerPrimitive := by
  intro n arity Gamma
  exact OrdinaryArithmeticQuotientPrimitiveProof.decodedCheckerPrimitive
    (fun ctx x y c => QuotientDirectCertificates.numericTest n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y c)
    (QuotientDirectPrimrecProof.numericDirectPrimitive n arity Gamma)

theorem actualCheckerCalibration : OrdinaryArithmeticDirectTargets.ActualCheckerCalibration := by
  intro n arity Gamma symbols S table x y c
  simp [directValue,contextCode]

theorem encodedCertificates (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (ctxCode x y : Nat) :
    (∃ c, directValue n arity Gamma (List.Vector.ofFn ![ctxCode,x,y,c]) = 1) ↔
      encodedDirect n arity Gamma ctxCode x y := by
  cases hctx : Encodable.decode (α := Context n) ctxCode with
  | none => simp only [directValue,encodedDirect,List.Vector.get_ofFn,Matrix.cons_val_zero,hctx,
      Option.any_none,Bool.toNat_false,Nat.zero_ne_one,exists_false,reduceCtorEq, false_and]
  | some ctx =>
    simp only [directValue,encodedDirect,List.Vector.get_ofFn,Matrix.cons_val_zero,hctx,
      Option.any_some,OrdinaryArithmeticQuotientProof.boolNatOne,Option.some.injEq]
    constructor
    · intro h
      obtain ⟨ss,ts,hs,ht,hd⟩ :=
        (QuotientDirectCertificatesProof.numericDirectCertificates n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y).mp h
      exact ⟨ctx,ss,ts,rfl,hs,ht,hd⟩
    · rintro ⟨ctx',ss,ts,hctx',hs,ht,hd⟩
      subst ctx'
      exact (QuotientDirectCertificatesProof.numericDirectCertificates n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y).mpr ⟨ss,ts,hs,ht,hd⟩

theorem encodedDirectFormula : OrdinaryArithmeticDirectTargets.EncodedDirectFormula := by
  intro n arity Gamma
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 4 (directValue n arity Gamma) (encodedCheckerPrimitive n arity Gamma)
  refine ⟨p,hp,?_⟩
  intro ctx x y
  rw [OrdinaryArithmeticQuotientProof.certificateGraphTruth]
  simp only [hp]
  exact encodedCertificates n arity Gamma ctx x y

theorem uniformDirectFormula : OrdinaryArithmeticDirectTargets.UniformDirectFormula := by
  intro n arity Gamma
  obtain ⟨p,_,h⟩ := encodedDirectFormula n arity Gamma
  refine ⟨certificateGraph p,?_⟩
  intro symbols S table source target
  simpa [encodedDirect,contextCode] using
    h (contextCode symbols S table) (Encodable.encode source) (Encodable.encode target)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticDirectProof
