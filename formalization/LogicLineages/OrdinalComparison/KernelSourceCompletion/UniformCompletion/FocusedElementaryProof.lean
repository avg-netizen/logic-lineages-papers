module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.FocusedElementaryTargets
public import LogicLineages.OrdinalComparison.QuadraticSeparationIterationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused

/-! Source-preserving extraction of UniformCompletion/ElementaryProof. Exact
signed order and all three primitive-recursive programmes are unchanged. -/

theorem exactSignedOrder : FocusedElementaryTargets.ExactSignedOrder := by
  intro d c t _ _ j k hj hk
  have hm := QuadraticSeparation.Proof.iteratePhi_strictMono t
  change
    ((Phi^[(sourceSignedDepth d c j t).toNat]) t <
      (Phi^[(sourceSignedDepth d c k t).toNat]) t ↔ j < k) ∧
    ((Phi^[(sourceSignedDepth d c j t).toNat]) t =
      (Phi^[(sourceSignedDepth d c k t).toNat]) t ↔ j = k) ∧
    ((Phi^[(sourceSignedDepth d c j t).toNat]) t ≤
      (Phi^[(sourceSignedDepth d c k t).toNat]) t ↔ j ≤ k)
  rw [hm.lt_iff_lt,hm.injective.eq_iff,hm.le_iff_le]
  unfold sourceSignedDepth at *
  omega

private theorem constant_primitive : Primrec degreeConstant :=
  Primrec.nat_mul.comp
    (Primrec.nat_mul.comp (Primrec.const 1000) Primrec.id) Primrec.id

private theorem threshold_primitive : Primrec degreeThreshold := by
  have hi : Primrec (fun p : Nat × Nat => p.1+1) := Primrec.succ.comp Primrec.fst
  have hn : Primrec (fun p : Nat × Nat =>
      max p.2 (100*degreeConstant p.1+100*(p.1+1))) :=
    Primrec.nat_max.comp Primrec.snd (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 100) (constant_primitive.comp Primrec.fst))
      (Primrec.nat_mul.comp (Primrec.const 100) hi))
  have hs : Primrec₂ (fun d v : Nat => if d+1 ≤ 3 then 16 else
      max v (100*degreeConstant d+100*(d+1))) :=
    (Primrec.ite (Primrec.nat_le.comp hi (Primrec.const 3)) (Primrec.const 16) hn).to₂
  apply (Primrec.nat_rec₁ 16 hs).of_eq
  intro d
  induction d with
  | zero => rfl
  | succ d ih => simp only [Nat.rec,degreeThreshold,ih]

theorem uniformTailPrograms : FocusedElementaryTargets.UniformTailPrograms := by
  refine ⟨constant_primitive,threshold_primitive,?_⟩
  let A := Nat × Nat × Nat × Int × Int
  have hd : Primrec (fun p : A => p.1) := Primrec.fst
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hj : Primrec (fun p : A => p.2.2.2.1.natAbs) :=
    LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hk : Primrec (fun p : A => p.2.2.2.2.natAbs) :=
    LayeredComparison.IntegerAlgorithms.Proof.abs_primitive.comp
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hC := constant_primitive.comp hd
  have hcross : Primrec (fun p : A => p.2.1+p.2.2.1+p.2.2.2.1.natAbs+p.2.2.2.2.natAbs+1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_add.comp hc he) hj) hk) (Primrec.const 1)
  have hselfc : Primrec (fun p : A => 2*p.2.1+2*p.2.2.2.1.natAbs+1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) hc)
      (Primrec.nat_mul.comp (Primrec.const 2) hj)) (Primrec.const 1)
  have hselfe : Primrec (fun p : A => 2*p.2.2.1+2*p.2.2.2.2.natAbs+1) :=
    Primrec.nat_add.comp (Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) he)
      (Primrec.nat_mul.comp (Primrec.const 2) hk)) (Primrec.const 1)
  exact Primrec.nat_max.comp (threshold_primitive.comp hd)
    (Primrec.nat_max.comp (Primrec.nat_mul.comp hC hcross)
      (Primrec.nat_max.comp (Primrec.nat_mul.comp hC hselfc) (Primrec.nat_mul.comp hC hselfe)))

end LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Focused
