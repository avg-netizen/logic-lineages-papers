module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedenceProof
open OrdinaryArithmetic OrdinaryArithmeticQuotient NumericPrecedenceCertificate RankedPrecedenceCertificate RankedPrecedenceCompleteness OrdinaryArithmeticPrecedence
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem valuePrimitive (n : Nat) : Primrec (rankValue n) := by
  have hg (i : Fin 2) : Primrec (fun v : List.Vector Nat 2 => v.get i) :=
    Primrec.vector_get.comp Primrec.id (Primrec.const i)
  exact (Primrec.dom_bool Bool.toNat).comp ((NumericPrecedenceCertificateProof.actualNumericRankPrimitive n).comp (hg 0) (hg 1))

theorem valueCalibration (n context certificate : Nat) :
    rankValue n (List.Vector.ofFn ![context,certificate]) = 1 ↔ numericRankTest n context certificate = true := by
  simp only [rankValue,List.Vector.get_ofFn,Matrix.cons_val_zero,Matrix.cons_val_one,OrdinaryArithmeticQuotientProof.boolNatOne]

theorem actualArithmeticRankFormula : OrdinaryArithmeticPrecedenceTargets.ActualArithmeticRankFormula := by
  intro n
  obtain ⟨p,hp⟩ := Proof.allPrimitiveFunctions 2 (rankValue n) (valuePrimitive n)
  refine ⟨p,hp,?_⟩
  intro context certificate
  rw [rankGraph,OrdinaryArithmeticProgramProof.appliedProgramGraphTruth,hp]
  exact (valueCalibration n context certificate).trans (NumericPrecedenceCertificateProof.actualNumericRankCalibration n context certificate)

theorem contextGraphTruth (p : Program 2) (v : Fin 1 → Nat) :
    (validContextGraph p).Realize v ↔ ∃ c : Nat, evaluate p (List.Vector.ofFn ![v 0,c]) = 1 := by
  rw [validContextGraph,OrdinaryArithmeticCompositionProof.existsFiniteTruth]
  simp only [OrdinaryArithmeticCompositionProof.applyGraphTruth,
    OrdinaryArithmeticProgramProof.programGraphTruth,Fin.cons_zero,Fin.cons_succ,
    OrdinaryArithmeticBetaProof.realize_succ,OrdinaryArithmeticBetaProof.realize_zero]
  constructor
  · rintro ⟨xs,h⟩
    exact ⟨xs 0,h⟩
  · rintro ⟨c,h⟩
    exact ⟨fun _ => c,h⟩

theorem actualArithmeticStrictContext : OrdinaryArithmeticPrecedenceTargets.ActualArithmeticStrictContext := by
  intro n
  obtain ⟨p,hp,_⟩ := actualArithmeticRankFormula n
  refine ⟨validContextGraph p,?_⟩
  intro context
  rw [contextGraphTruth]
  simp only [hp,Matrix.cons_val_zero,valueCalibration]
  exact NumericPrecedenceCertificateProof.actualNumericRankExistence n context

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticPrecedenceProof
