module

public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientPrimitiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticProgramProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesProof

@[expose] public section

namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientProof

open FirstOrder Language Source OrdinaryArithmetic OrdinaryArithmeticQuotient
open OrdinaryArithmeticQuotientTargets NumberedQuotientPaths NumberedCopyCertificate
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem boolNatOne (b : Bool) : b.toNat = 1 ↔ b = true := by cases b <;> simp

theorem certificateGraphTruth (p : Program 4) (v : Fin 3 → Nat) :
    (certificateGraph p).Realize v ↔
      ∃ c : Nat, evaluate p (List.Vector.ofFn ![v 0, v 1, v 2, c]) = 1 := by
  rw [certificateGraph, OrdinaryArithmeticCompositionProof.existsFiniteTruth]
  simp only [OrdinaryArithmeticCompositionProof.applyGraphTruth,
    OrdinaryArithmeticProgramProof.programGraphTruth, Fin.cons_zero, Fin.cons_succ,
    OrdinaryArithmeticBetaProof.realize_succ, OrdinaryArithmeticBetaProof.realize_zero]
  constructor
  · rintro ⟨xs, h⟩
    refine ⟨xs 0, ?_⟩
    exact h
  · rintro ⟨c, h⟩
    exact ⟨fun _ => c, h⟩

theorem encodedEdgeCertificates (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (ctxCode x y : Nat) :
    (∃ c, edgeValue n arity Gamma (List.Vector.ofFn ![ctxCode, x, y, c]) = 1) ↔
    ∃ ctx : Context n, Encodable.decode (α := Context n) ctxCode = some ctx ∧
      QuotientEdge n arity ctx.1.1 ctx.1.2 (tableAbove ctx.2) Gamma x y := by
  cases hctx : Encodable.decode (α := Context n) ctxCode with
  | none => simp [edgeValue, hctx]
  | some ctx =>
    simp only [edgeValue, List.Vector.get_ofFn, Matrix.cons_val_zero, hctx,
      Option.any_some, boolNatOne]
    simpa using
      NumberedNumericQuotientEdgeProof.numericQuotientEdge n arity ctx.1.1 ctx.1.2 Gamma ctx.2 x y

theorem encodedPositiveCertificates (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (ctxCode x y : Nat) :
    (∃ c, positiveValue n arity Gamma (List.Vector.ofFn ![ctxCode, x, y, c]) = 1) ↔
    ∃ ctx : Context n, Encodable.decode (α := Context n) ctxCode = some ctx ∧
      PositivePath (QuotientEdge n arity ctx.1.1 ctx.1.2 (tableAbove ctx.2) Gamma) x y := by
  cases hctx : Encodable.decode (α := Context n) ctxCode with
  | none => simp [positiveValue, hctx]
  | some ctx =>
    simp only [positiveValue, List.Vector.get_ofFn, Matrix.cons_val_zero, hctx,
      Option.any_some, boolNatOne]
    simpa using
      NumberedQuotientPathCertificatesProof.numericPositivePathCertificates n arity
        ctx.1.1 ctx.1.2 Gamma ctx.2 x y

theorem encodedHAndPositiveR : EncodedHAndPositiveR := by
  intro n arity Gamma
  obtain ⟨he, hr⟩ := OrdinaryArithmeticQuotientPrimitiveProof.encodedCheckersPrimitive n arity Gamma
  obtain ⟨pH, hpH⟩ := Proof.allPrimitiveFunctions 4 (edgeValue n arity Gamma) he
  obtain ⟨pR, hpR⟩ := Proof.allPrimitiveFunctions 4 (positiveValue n arity Gamma) hr
  refine ⟨pH, pR, hpH, hpR, ?_, ?_⟩
  · intro ctxCode x y
    rw [certificateGraphTruth]
    simp only [hpH]
    exact encodedEdgeCertificates n arity Gamma ctxCode x y
  · intro ctxCode x y
    rw [certificateGraphTruth]
    simp only [hpR]
    exact encodedPositiveCertificates n arity Gamma ctxCode x y

theorem uniformSharedWindowFormulas : UniformSharedWindowFormulas := by
  intro n arity Gamma
  obtain ⟨pH, pR, _, _, hH, hR⟩ := encodedHAndPositiveR n arity Gamma
  refine ⟨certificateGraph pH, certificateGraph pR, ?_⟩
  intro symbols S table x y
  constructor
  · simpa [contextCode] using hH (contextCode symbols S table) x y
  · simpa [contextCode] using hR (contextCode symbols S table) x y

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticQuotientProof
