module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySignTargets
public import LogicLineages.OrdinalComparison.SignedPhiSeparationProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign.Proof
open IntegerAlgorithms.Proof SignedShiftCollection
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem row_pr : Primrec (fun E : Expression => E.1) := Primrec.fst
private theorem slope_pr : Primrec (fun E : Expression => E.2.1) := Primrec.fst.comp Primrec.snd
private theorem constant_pr : Primrec (fun E : Expression => E.2.2) := Primrec.snd.comp Primrec.snd

private theorem value_pr : Primrec₂ value :=
  add_primitive.comp
    (add_primitive.comp
      (SignedPhiSeparation.Proof.value_primitive.comp (row_pr.comp Primrec.fst) Primrec.snd)
      (mul_primitive.comp (slope_pr.comp Primrec.fst) (ofNat_primitive.comp Primrec.snd)))
    (constant_pr.comp Primrec.fst)

private theorem domain_pr : Primrec domainBound :=
  SignedShiftCollection.Proof.domainOffset_primitive.comp row_pr
private theorem delta_pr : Primrec (fun E : Expression => SignedPhiSeparation.delta E.1) :=
  SignedPhiSeparation.Proof.delta_primitive.comp row_pr
private theorem mass_pr : Primrec (fun E : Expression => E.2.1.natAbs) :=
  abs_primitive.comp slope_pr
private theorem intercept_pr : Primrec (fun E : Expression => E.2.2.natAbs) :=
  abs_primitive.comp constant_pr
private theorem cancelled_test : PrimrecPred (fun E : Expression => collected E.1 = []) :=
  Primrec.eq.comp (SignedShiftCollection.Proof.collected_primitive.comp row_pr) (Primrec.const [])

attribute [local irreducible] SignedPhiSeparation.delta SignedShiftCollection.collected domainBound

private theorem threshold_pr : Primrec threshold := by
  have hc : Primrec (fun E : Expression => max (domainBound E) (E.2.2.natAbs + 1)) :=
    Primrec.nat_max.comp domain_pr
      (Primrec.nat_add.comp intercept_pr (Primrec.const 1))
  have hm : Primrec (fun E : Expression =>
      E.2.1.natAbs + E.2.1.natAbs * SignedPhiSeparation.delta E.1 + E.2.2.natAbs + 1) :=
    Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp mass_pr (Primrec.nat_mul.comp mass_pr delta_pr))
        intercept_pr) (Primrec.const 1)
  exact Primrec.ite cancelled_test hc (Primrec.nat_add.comp delta_pr hm)

private theorem tail_pr : Primrec tailSign :=
  Primrec.ite cancelled_test
    (Primrec.ite (Primrec.eq.comp slope_pr (Primrec.const (0 : Int)))
      (sign_primitive.comp constant_pr) (sign_primitive.comp slope_pr))
    (sign_primitive.comp (SignedShiftCollection.Proof.leadingCoefficient_primitive.comp row_pr))

theorem actualPrimitiveRecursion : Targets.ActualPrimitiveRecursion :=
  ⟨value_pr, domain_pr, threshold_pr, tail_pr⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySign.Proof
