module
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxTargets
public import LogicLineages.OrdinalComparison.WWDefaultPolicyProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

theorem defaultSyntaxBoxTailCorrect : Targets.DefaultSyntaxBoxTailCorrect := by
  intro Γ n f g
  rw [defaultPolicyBoxTail Γ n f g]
  unfold defaultBoxTailCode
  by_cases hn : n=0
  · simp [hn, typedCode, code, node]
  · simp only [if_neg hn]
    have hr : repeatCode n 1 = typedCode (AdmissibleAssignment.numeral defaultPolicy n : OrdinalExpression Γ) := by
      unfold AdmissibleAssignment.numeral
      rw [defaultPolicyRepeatEquality Γ .numeral (by decide)]
      exact ordinalSyntaxRepeatCorrect Γ .numeral n .one
    rw [hr]
    rfl

theorem defaultSyntaxApplicationCorrect : Targets.DefaultSyntaxApplicationCorrect := by
  intro Γ σ τ f g
  apply List.ext_getElem
  · simp [defaultApplicationCode, vectorCode]
  · intro j hj hk
    have hj' : j < τ.level+1 := by simpa [defaultApplicationCode] using hj
    simp only [defaultApplicationCode, vectorCode, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    unfold AdmissibleAssignment.application AdmissibleAssignment.box
    by_cases hzero : j=0
    · simp only [hzero, if_true]
      have hpos := ordinalSyntaxBoxPositiveCorrect Γ _ _ f g 1
      dsimp only [vectorCode] at hpos
      rw [hpos]
      have hf : (List.ofFn (fun i => typedCode (f i))).getD 0 0 = typedCode (f 0) := by
        simp [List.getD_eq_getElem?_getD]
      have hg : (List.ofFn (fun i => typedCode (g i))).getD 0 0 = typedCode (g 0) := by
        simp [List.getD_eq_getElem?_getD]
      rw [hf, hg, defaultSyntaxBoxTailCorrect Γ σ.level (f 0) (g 0)]
      rfl
    · simp only [if_neg hzero]
      exact ordinalSyntaxBoxPositiveCorrect Γ _ _ f g j
private theorem node_primitive {α : Type} [Primcodable α] {tag a b : α → Nat}
    (ht : Primrec tag) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node (tag x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp ha hb)) ht

theorem defaultSyntaxApplicationPrimitiveRecursive : Targets.DefaultSyntaxApplicationPrimitiveRecursive := by
  let P := Nat × Nat × List Nat × List Nat
  have hlen : Primrec (fun p : P => p.1+1) := Primrec.succ.comp Primrec.fst
  apply Primrec.list_map (Primrec.list_range.comp hlen)
  change Primrec (fun q : P × Nat => if q.2=0 then
    node 6 (boxPositive q.1.2.1 q.1.2.2.1 q.1.2.2.2 1)
      (defaultBoxTailCode q.1.2.1 (q.1.2.2.1.getD 0 0) (q.1.2.2.2.getD 0 0))
    else boxPositive q.1.2.1 q.1.2.2.1 q.1.2.2.2 q.2)
  have hn : Primrec (fun q : P × Nat => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hf : Primrec (fun q : P × Nat => q.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hg : Primrec (fun q : P × Nat => q.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have bp {i : P × Nat → Nat} (hi : Primrec i) : Primrec (fun q => boxPositive q.1.2.1 q.1.2.2.1 q.1.2.2.2 (i q)) :=
    ordinalSyntaxBoxOperationsPrimitiveRecursive.1.comp (hn.pair (hf.pair (hg.pair hi)))
  have hf0 := (Primrec.list_getD 0).comp hf (Primrec.const 0)
  have hg0 := (Primrec.list_getD 0).comp hg (Primrec.const 0)
  have ht : Primrec (fun q : P × Nat => defaultBoxTailCode q.1.2.1 (q.1.2.2.1.getD 0 0) (q.1.2.2.2.getD 0 0)) :=
    Primrec.ite (Primrec.eq.comp hn (Primrec.const 0))
      (node_primitive (Primrec.const 4) hf0 hg0)
      (node_primitive (Primrec.const 4) hf0 (node_primitive (Primrec.const 4) hg0
        (ordinalSyntaxSumOperationsPrimitiveRecursive.2.comp hn (Primrec.const 1))))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (node_primitive (Primrec.const 6) (bp (Primrec.const 1)) ht) (bp Primrec.snd)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
