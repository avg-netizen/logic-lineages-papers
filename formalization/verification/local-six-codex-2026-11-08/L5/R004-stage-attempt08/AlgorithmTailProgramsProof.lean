module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmExpansionProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
open PolynomialGraphCompletion WordGuardCompletion Algorithm

theorem rowSourceTail_primitive : Primrec rowSourceTail := by
  have hs := Primrec.list_map active_primitive (sourceTail_primitive.comp Primrec.snd).to₂
  have hi : Primrec (fun p : Row × Item => (active p.1).map (collisionTail p.2)) :=
    Primrec.list_map (active_primitive.comp Primrec.fst)
      (collisionTail_primitive.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  have hc := Primrec.list_flatMap active_primitive hi.to₂
  exact Primrec.nat_max.comp rowTail_primitive
    (Primrec.nat_max.comp (foldMax_primitive.comp hs) (foldMax_primitive.comp hc))

theorem itemAbsMass_primitive : Primrec (fun xs : List Item => (xs.map (fun a => a.1.natAbs)).sum) :=
  natSum_primitive.comp (Primrec.list_map Primrec.id
    (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp
      (Primrec.fst.comp Primrec.snd)).to₂)

theorem nonlinearMass_primitive : Primrec nonlinearMass := itemAbsMass_primitive.comp active_primitive

theorem linearMass_primitive : Primrec linearMass := itemAbsMass_primitive.comp linearPart_primitive

theorem preimageOffset_primitive : Primrec preimageOffset :=
  natSum_primitive.comp (Primrec.list_map active_primitive
    (WordGuardCompletion.Proof.wordOffset_primitive.comp (preimage_primitive.comp Primrec.snd)).to₂)

theorem signPayment_primitive : Primrec signPayment :=
  Primrec.nat_mul.comp (Primrec.const 64)
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp
          (Primrec.nat_add.comp nonlinearMass_primitive linearMass_primitive)
          (Primrec.nat_mul.comp linearMass_primitive preimageOffset_primitive))
        (LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp Primrec.fst)) (Primrec.const 1))

theorem signTail_primitive : Primrec signTail :=
  Primrec.nat_max.comp rowSourceTail_primitive
    (foldMax_primitive.comp (Primrec.list_map active_primitive
      (WordGuardCompletion.Proof.reachTail_primitive.comp
        ((preimage_primitive.comp Primrec.snd).pair (signPayment_primitive.comp Primrec.fst))).to₂))

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.AlgorithmPrograms
