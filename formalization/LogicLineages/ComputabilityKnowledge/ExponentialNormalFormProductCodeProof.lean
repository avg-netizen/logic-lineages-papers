module

public import LogicLineages.ComputabilityKnowledge.Comparators.ExponentialNormalFormProductCode
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormCodeOperationsProof
public import LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductProof

@[expose] public section

/-! Exact executable source N2 constructor, authored in Codex after the
independent comparator compiled. Its reference is the existing mathematical
finite-map product; the natural-number program is additionally proved uniform
primitive recursive, without an assumed correctness or effectivity oracle.
-/
namespace LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCodeProof

open ExponentialNormalForm ExponentialNormalFormProduct
open ExponentialNormalFormCodec ExponentialHereditaryCodec
open ExponentialNormalFormCodeOperations ExponentialNormalFormProductCode
open ExponentialNormalFormCodecProof ExponentialHereditaryCodecProof
open ExponentialNormalFormCodeOperationsProof
open ExponentialNormalFormCodeOperationsEffectivity
  (pr_addCode pr_removeCode pr_raiseCode pr_constantCoefficientCode pr_canonicalEntries)

theorem scale_zero {d : Nat} (k : Nat) : scaleAffine k (0 : Affine d) = 0 := by
  funext i
  simp [scaleAffine]

theorem scale_add {d : Nat} (k : Nat) (a b : Affine d) :
    scaleAffine k (a + b) = scaleAffine k a + scaleAffine k b := by
  funext i
  simp [scaleAffine, Nat.mul_add]

theorem product_succ_zero {d : Nat} (h : Nat) (f : Form d (h + 1)) :
    exponentialProduct (h + 1) f 0 = 0 :=
  Finsupp.sum_zero_index

theorem product_succ_add {d : Nat} (h : Nat) (f g₁ g₂ : Form d (h + 1)) :
    exponentialProduct (h + 1) f (g₁ + g₂) =
      exponentialProduct (h + 1) f g₁ + exponentialProduct (h + 1) f g₂ := by
  unfold exponentialProduct
  exact Finsupp.sum_add_index'
    (fun key => by rw [scale_zero, Finsupp.single_zero])
    (fun key a b => by rw [scale_add, Finsupp.single_add])

theorem product_succ_single {d : Nat} (h : Nat) (f : Form d (h + 1))
    (key : Form d h) (c : Affine d) :
    exponentialProduct (h + 1) f (Finsupp.single key c) =
      Finsupp.single (addForm (h + 1) (removeConstant (h + 1) f) (raiseForm h key))
        (scaleAffine (2 ^ constantCoefficient (h + 1) f) c) := by
  unfold exponentialProduct
  apply Finsupp.sum_single_index
  rw [scale_zero, Finsupp.single_zero]

theorem entriesDecode_product (d h a : Nat) (es : MapCode) :
    entriesDecode d (h + 1) (es.map (fun e =>
      (addCode d (h + 1) (removeCode d (h + 1) a) (raiseCode d h e.1),
        coeffScale d (2 ^ constantCoefficientCode d (h + 1) a) e.2))) =
      exponentialProduct (h + 1) (formDecode d (h + 1) a) (entriesDecode d h es) := by
  induction es with
  | nil => exact (product_succ_zero h _).symm
  | cons e es ih =>
      change Finsupp.single
        (formDecode d (h + 1) (addCode d (h + 1) (removeCode d (h + 1) a)
          (raiseCode d h e.1)))
        (coeffDecode d (coeffScale d (2 ^ constantCoefficientCode d (h + 1) a) e.2)) +
        entriesDecode d (h + 1) (es.map (fun e =>
          (addCode d (h + 1) (removeCode d (h + 1) a) (raiseCode d h e.1),
            coeffScale d (2 ^ constantCoefficientCode d (h + 1) a) e.2))) =
        exponentialProduct (h + 1) (formDecode d (h + 1) a)
          (Finsupp.single (formDecode d h e.1) (coeffDecode d e.2) + entriesDecode d h es)
      rw [product_succ_add, product_succ_single, ih,
        (additionCodes d (h + 1) _ _).2,
        (constantRemovalCodes d (h + 1) a).2.2,
        (heightTransportCodes d h e.1).2,
        constantCoefficientCode_correct, decode_scale]
      rfl

theorem sourceImplementation : Comparators.ExponentialNormalFormProductCode.SourceImplementation := by
  intro d h a b
  cases h with
  | zero =>
      refine ⟨canonical_encode_normalizeMap d 0 _ ?_, ?_⟩
      · intro e he
        simp only [List.mem_singleton] at he
        subst e
        exact (constantRemovalCodes d 0 a).2.1
      · change formDecode d 1 (Encodable.encode (normalizeMap d
          [(removeCode d 0 a,
            coeffScale d (2 ^ constantCoefficientCode d 0 a) (parseCoefficients b))])) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap]
        change Finsupp.single (formDecode d 0 (removeCode d 0 a))
          (coeffDecode d (coeffScale d (2 ^ constantCoefficientCode d 0 a)
            (parseCoefficients b))) + 0 = _
        rw [(constantRemovalCodes d 0 a).2.2, constantCoefficientCode_correct,
          decode_scale, add_zero]
        rfl
  | succ h =>
      refine ⟨canonical_encode_normalizeMap d (h + 1) _ ?_, ?_⟩
      · intro e he
        obtain ⟨c, _, rfl⟩ := List.mem_map.mp he
        exact (additionCodes d (h + 1) _ _).1
      · change formDecode d ((h + 1) + 1) (Encodable.encode (normalizeMap d
          ((canonicalEntries d (h + 1) b).map (fun e =>
            (addCode d (h + 1) (removeCode d (h + 1) a) (raiseCode d h e.1),
              coeffScale d (2 ^ constantCoefficientCode d (h + 1) a) e.2))))) = _
        rw [formDecode_succ_encode, entriesDecode_normalizeMap,
          entriesDecode_product, canonicalEntries_decode]

private theorem pr_powTwo : Primrec (fun n : Nat => 2 ^ n) := by
  have h : Primrec (Nat.rec 1 (fun _ r : Nat => r * 2)) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [ih, pow_succ]

theorem actualPrimitiveRecursion : Comparators.ExponentialNormalFormProductCode.ActualPrimitiveRecursion := by
  let d : Nat × Nat × Nat × Nat → Nat := fun p => p.1
  let h : Nat × Nat × Nat × Nat → Nat := fun p => p.2.1
  let a : Nat × Nat × Nat × Nat → Nat := fun p => p.2.2.1
  let b : Nat × Nat × Nat × Nat → Nat := fun p => p.2.2.2
  have hd : Primrec d := Primrec.fst
  have hh : Primrec h := Primrec.fst.comp Primrec.snd
  have ha : Primrec a := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec b := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun p => removeCode (d p) (h p) (a p)) :=
    pr_removeCode.comp (hd.pair (hh.pair ha))
  have hk : Primrec (fun p => 2 ^ constantCoefficientCode (d p) (h p) (a p)) :=
    pr_powTwo.comp (pr_constantCoefficientCode.comp (hd.pair (hh.pair ha)))
  have hcoeff : Primrec (fun p =>
      coeffScale (d p) (2 ^ constantCoefficientCode (d p) (h p) (a p))
        (parseCoefficients (b p))) :=
    pr_scale.comp (hd.pair (hk.pair (pr_parseCoefficients.comp hb)))
  have hbase := Primrec.encode.comp (pr_normalizeMap.comp
    (hd.pair (Primrec.list_cons.comp (hr.pair hcoeff) (Primrec.const []))))
  have he : Primrec (fun p => canonicalEntries (d p) (h p) (b p)) :=
    pr_canonicalEntries.comp (hd.pair (hh.pair hb))
  have hstep : Primrec₂ (fun (p : Nat × Nat × Nat × Nat) (e : Nat × CoeffCode) =>
      (addCode (d p) (h p) (removeCode (d p) (h p) (a p)) (raiseCode (d p) (h p - 1) e.1),
        coeffScale (d p) (2 ^ constantCoefficientCode (d p) (h p) (a p)) e.2)) := by
    have hekey : Primrec (fun x : (Nat × Nat × Nat × Nat) × (Nat × CoeffCode) => x.2.1) :=
      Primrec.fst.comp Primrec.snd
    have hecoeff : Primrec (fun x : (Nat × Nat × Nat × Nat) × (Nat × CoeffCode) => x.2.2) :=
      Primrec.snd.comp Primrec.snd
    have hraise := pr_raiseCode.comp ((hd.comp Primrec.fst).pair
      ((Primrec.nat_sub.comp (hh.comp Primrec.fst) (Primrec.const 1)).pair hekey))
    have hsum := pr_addCode.comp ((hd.comp Primrec.fst).pair
      ((hh.comp Primrec.fst).pair ((hr.comp Primrec.fst).pair hraise)))
    have hscale := pr_scale.comp ((hd.comp Primrec.fst).pair
      ((hk.comp Primrec.fst).pair hecoeff))
    exact (hsum.pair hscale).to₂
  have hsucc := Primrec.encode.comp (pr_normalizeMap.comp
    (hd.pair (Primrec.list_map he hstep)))
  apply (Primrec.ite (Primrec.eq.comp hh (Primrec.const 0)) hbase hsucc).of_eq
  rintro ⟨d, h, a, b⟩
  cases h <;> rfl

theorem productCode : Comparators.ExponentialNormalFormProductCode.Target :=
  ⟨sourceImplementation, actualPrimitiveRecursion⟩

end LogicLineages.ComputabilityKnowledge.ExponentialNormalFormProductCodeProof
