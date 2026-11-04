module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeCalibrationProof
public import LogicLineages.OrdinalComparison.LayeredComparison.FiniteGraphProof
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import Mathlib.Tactic.SplitIfs
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeProof
attribute [local irreducible] Nat.sqrt Nat.unpair

/-- One numeric recursion graph covers BOTH literal syntaxes. The Boolean tag
selects matrix/term; every child code is smaller, even matrix-to-term calls. -/
private abbrev Call := Bool × (Nat × (Nat × Nat))
private def radix (p : Call) : Nat := if p.1 = true then 8 else 10
private def tag (p : Call) : Nat := p.2.1 % radix p
private def quotient (p : Call) : Nat := p.2.1 / radix p
private def child (p : Call) (matrix : Bool) (code : Nat) : Call := (matrix, code, p.2.2)
private def children (p : Call) : List Call :=
  if tag p = 0 ∨ tag p = 1 then []
  else if p.1 = true then
    if tag p = 2 ∨ tag p = 3 then
      [child p false (quotient p).unpair.1, child p false (quotient p).unpair.2]
    else if tag p = 4 then [child p false (quotient p).unpair.2]
    else if tag p = 5 then [child p true (quotient p)]
    else [child p true (quotient p).unpair.1, child p true (quotient p).unpair.2]
  else if tag p = 2 ∨ tag p = 3 then
    [child p false (quotient p).unpair.1, child p false (quotient p).unpair.2]
  else if tag p = 4 ∨ tag p = 5 then [child p false (quotient p).unpair.2]
  else [child p false (quotient p)]

private def assemble (p : Call) (xs : List Nat) : Nat :=
  if p.1 = true then
    if tag p = 0 then 0
    else if tag p = 1 then 1
    else if tag p = 2 ∨ tag p = 3 then
      8 * Nat.pair (xs.getD 0 0) (xs.getD 1 0) + tag p
    else if tag p = 4 then 8 * Nat.pair (quotient p).unpair.1 (xs.getD 0 0) + 4
    else if tag p = 5 then 8 * xs.getD 0 0 + 5
    else 8 * Nat.pair (xs.getD 0 0) (xs.getD 1 0) + tag p
  else if tag p = 0 then p.2.1
  else if tag p = 1 then if quotient p = p.2.2.1 then p.2.2.2 else p.2.1
  else if tag p = 2 ∨ tag p = 3 then
    10 * Nat.pair (xs.getD 0 0) (xs.getD 1 0) + tag p
  else if tag p = 4 ∨ tag p = 5 then
    10 * Nat.pair (quotient p).unpair.1 (xs.getD 0 0) + tag p
  else 10 * xs.getD 0 0 + tag p

private def joint (p : Call) : Nat :=
  if p.1 = true then WindowCode.matrixSubstitute p.2.2.1 p.2.2.2 p.2.1
  else WindowCode.termSubstitute p.2.2.1 p.2.2.2 p.2.1

private theorem decreasing : ∀ p q : Call, q ∈ children p → q.2.1 < p.2.1 := by
  intro p q hq
  by_cases hleaf : tag p = 0 ∨ tag p = 1
  · simp [children, hleaf] at hq
  have hrad : 1 < radix p := by unfold radix; split <;> decide
  have hpos : 0 < p.2.1 := by
    by_contra hn
    have hz : p.2.1 = 0 := by omega
    have ht : tag p = 0 := by simp [tag, hz]
    exact hleaf (Or.inl ht)
  have hd : quotient p < p.2.1 := Nat.div_lt_self hpos hrad
  have hl := Nat.unpair_left_le (quotient p)
  have hr := Nat.unpair_right_le (quotient p)
  rcases q with ⟨f, n, i, r⟩
  unfold children at hq
  split_ifs at hq <;>
    simp_all only [List.mem_cons, List.not_mem_nil,
      or_false, child, Prod.mk.injEq]
  all_goals omega

private theorem equation (p : Call) : joint p = assemble p ((children p).map joint) := by
  rcases p with ⟨flag, code, i, r⟩
  cases flag with
  | false =>
    change WindowCode.termSubstitute i r code = _
    rw [WindowCode.termSubstitute]
    split_ifs <;> simp_all [children, assemble, joint, tag, quotient, radix, child]
  | true =>
    change WindowCode.matrixSubstitute i r code = _
    rw [WindowCode.matrixSubstitute]
    split_ifs <;> simp_all [children, assemble, joint, tag, quotient, radix, child]

private theorem flag_primitive : Primrec (fun p : Call => p.1) := Primrec.fst
private theorem code_primitive : Primrec (fun p : Call => p.2.1) := Primrec.fst.comp Primrec.snd
private theorem params_primitive : Primrec (fun p : Call => p.2.2) := Primrec.snd.comp Primrec.snd
private theorem radix_primitive : Primrec radix :=
  Primrec.ite (Primrec.eq.comp flag_primitive (Primrec.const true)) (Primrec.const 8) (Primrec.const 10)
private theorem tag_primitive : Primrec tag := Primrec.nat_mod.comp code_primitive radix_primitive
private theorem quotient_primitive : Primrec quotient := Primrec.nat_div.comp code_primitive radix_primitive
private theorem left_primitive : Primrec (fun p : Call => (quotient p).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun p : Call => (quotient p).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
private theorem tag_is (n : Nat) : PrimrecPred (fun p : Call => tag p = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem flag_is : PrimrecPred (fun p : Call => p.1 = true) :=
  Primrec.eq.comp flag_primitive (Primrec.const true)
private theorem child_primitive (b : Bool) {f : Call → Nat} (hf : Primrec f) :
    Primrec (fun p => child p b (f p)) :=
  (Primrec.const b).pair (hf.pair params_primitive)
private theorem singleton_primitive (b : Bool) {f : Call → Nat} (hf : Primrec f) :
    Primrec (fun p => [child p b (f p)]) :=
  Primrec.list_cons.comp (child_primitive b hf) (Primrec.const [])
private theorem pair_children_primitive (b : Bool) :
    Primrec (fun p : Call => [child p b (quotient p).unpair.1,
      child p b (quotient p).unpair.2]) :=
  Primrec.list_cons.comp (child_primitive b left_primitive)
    (singleton_primitive b right_primitive)

private theorem children_primitive : Primrec children :=
  Primrec.ite ((tag_is 0).or (tag_is 1)) (Primrec.const [])
    (Primrec.ite flag_is
      (Primrec.ite ((tag_is 2).or (tag_is 3)) (pair_children_primitive false)
        (Primrec.ite (tag_is 4) (singleton_primitive false right_primitive)
          (Primrec.ite (tag_is 5) (singleton_primitive true quotient_primitive)
            (pair_children_primitive true))))
      (Primrec.ite ((tag_is 2).or (tag_is 3)) (pair_children_primitive false)
        (Primrec.ite ((tag_is 4).or (tag_is 5)) (singleton_primitive false right_primitive)
          (singleton_primitive false quotient_primitive))))

private theorem assemble_primitive : Primrec₂ assemble := by
  let C := Call × List Nat
  have ht : Primrec (fun p : C => tag p.1) := tag_primitive.comp Primrec.fst
  have hq : Primrec (fun p : C => quotient p.1) := quotient_primitive.comp Primrec.fst
  have hl : Primrec (fun p : C => (quotient p.1).unpair.1) := left_primitive.comp Primrec.fst
  have hc : Primrec (fun p : C => p.1.2.1) := code_primitive.comp Primrec.fst
  have hi : Primrec (fun p : C => p.1.2.2.1) := Primrec.fst.comp (params_primitive.comp Primrec.fst)
  have hr : Primrec (fun p : C => p.1.2.2.2) := Primrec.snd.comp (params_primitive.comp Primrec.fst)
  have h0 : Primrec (fun p : C => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : C => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  have hb (b : Nat) : Primrec (fun p : C => b * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + tag p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const b) (Primrec₂.natPair.comp h0 h1)) ht
  have hf (b : Nat) : Primrec (fun p : C => b * Nat.pair (quotient p.1).unpair.1 (p.2.getD 0 0) + tag p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const b) (Primrec₂.natPair.comp hl h0)) ht
  have hu (b : Nat) : Primrec (fun p : C => b * p.2.getD 0 0 + tag p.1) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const b) h0) ht
  have hdiv : Primrec (fun p : C => 8 * Nat.pair (quotient p.1).unpair.1 (p.2.getD 0 0) + 4) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp hl h0)) (Primrec.const 4)
  have hneg : Primrec (fun p : C => 8 * p.2.getD 0 0 + 5) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) h0) (Primrec.const 5)
  have hvar : Primrec (fun p : C => if quotient p.1 = p.1.2.2.1 then p.1.2.2.2 else p.1.2.1) :=
    Primrec.ite (Primrec.eq.comp hq hi) hr hc
  exact Primrec.ite (flag_is.comp Primrec.fst)
    (Primrec.ite ((tag_is 0).comp Primrec.fst) (Primrec.const 0)
      (Primrec.ite ((tag_is 1).comp Primrec.fst) (Primrec.const 1)
        (Primrec.ite (((tag_is 2).or (tag_is 3)).comp Primrec.fst) (hb 8)
          (Primrec.ite ((tag_is 4).comp Primrec.fst) hdiv
            (Primrec.ite ((tag_is 5).comp Primrec.fst) hneg (hb 8))))))
    (Primrec.ite ((tag_is 0).comp Primrec.fst) hc
      (Primrec.ite ((tag_is 1).comp Primrec.fst) hvar
        (Primrec.ite (((tag_is 2).or (tag_is 3)).comp Primrec.fst) (hb 10)
          (Primrec.ite (((tag_is 4).or (tag_is 5)).comp Primrec.fst) (hf 10) (hu 10)))))

private theorem joint_computable : Computable joint :=
  (FiniteGraph.Proof.exactDecreasingGraph Call Nat children assemble (fun p => p.2.1)
    children_primitive.to_comp assemble_primitive.to_comp code_primitive.to_comp
    joint decreasing equation).2

theorem term_computable : Computable
    (fun p : Nat × (Nat × Nat) => WindowCode.termSubstitute p.2.1 p.2.2 p.1) := by
  apply (joint_computable.comp ((Computable.const false).pair
    (Computable.id : Computable (fun p : Nat × (Nat × Nat) => p)))).of_eq
  intro p
  rfl

theorem matrix_computable : Computable
    (fun p : Nat × (Nat × Nat) => WindowCode.matrixSubstitute p.2.1 p.2.2 p.1) := by
  apply (joint_computable.comp ((Computable.const true).pair
    (Computable.id : Computable (fun p : Nat × (Nat × Nat) => p)))).of_eq
  intro p
  rfl

private theorem binary_primitive (base label : Nat) :
    Primrec₂ (fun a b : Nat => base * Nat.pair a b + label) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair)
    (Primrec.const label)

private theorem unary_primitive (base label : Nat) :
    Primrec (fun a : Nat => base * a + label) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec.id)
    (Primrec.const label)

private theorem numeral_primitive : Primrec WindowCode.numeral :=
  Primrec.nat_mul.comp (Primrec.const 10) Primrec.id
private theorem var_primitive : Primrec WindowCode.var := unary_primitive 10 1
private theorem add_primitive : Primrec₂ WindowCode.add := binary_primitive 10 2
private theorem subtract_primitive : Primrec₂ WindowCode.subtract := binary_primitive 10 3
private theorem multiply_primitive : Primrec₂ WindowCode.multiply := binary_primitive 10 4
private theorem phi_primitive : Primrec WindowCode.phi := unary_primitive 10 6
private theorem less_primitive : Primrec₂ WindowCode.less := binary_primitive 8 3
private theorem negative_primitive : Primrec WindowCode.negative := unary_primitive 8 5
private theorem conjunction_primitive : Primrec₂ WindowCode.conjunction := binary_primitive 8 6
private theorem disjunction_primitive : Primrec₂ WindowCode.disjunction := binary_primitive 8 7

private theorem toNat_primitive : Primrec Int.toNat := by
  apply (Primrec.ite
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 0) IntegerAlgorithms.Proof.abs_primitive).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem shift_primitive : Primrec₂ WindowCode.shift :=
  subtract_primitive.comp
    (add_primitive.comp Primrec.fst (numeral_primitive.comp (toNat_primitive.comp Primrec.snd)))
    (numeral_primitive.comp (toNat_primitive.comp
      (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd)))

private theorem any_primitive : Primrec WindowCode.any :=
  Primrec.list_foldr Primrec.id (Primrec.const 1)
    (disjunction_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem map_computable {A B C : Type} [Primcodable A] [Primcodable B]
    [Primcodable C] [Inhabited B] {xs : A → List B} {f : A → B → C}
    (hx : Computable xs) (hf : Computable₂ f) : Computable (fun a => (xs a).map (f a)) := by
  have hs : Computable₂ (fun a : A => fun p : B × List C => f a p.1 :: p.2) :=
    Primrec.list_cons.to_comp.comp
      (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr_cons, List.map_cons, ih]

theorem finite_computable : Computable WindowCode.finiteWindow := by
  let P := WindowCode.Input
  have hi : Primrec (fun p : P => p.1) := Primrec.fst
  have ha : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have he : Primrec (fun p : P => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun p : P => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hp : Primrec (fun p : P => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hv : Primrec (fun p : P => WindowCode.var p.1) := var_primitive.comp hi
  have hs : Primrec (fun p : P => WindowCode.shift (WindowCode.var p.1) p.2.2.1) :=
    shift_primitive.comp hv he
  have hpa : Primrec (fun p : P => WindowCode.phi p.2.1) := phi_primitive.comp ha
  have hps : Primrec (fun p : P => WindowCode.phi (WindowCode.shift (WindowCode.var p.1) p.2.2.1)) :=
    phi_primitive.comp hs
  have hat : Primrec₂ WindowCode.atMost :=
    negative_primitive.comp (less_primitive.comp Primrec.snd Primrec.fst)
  have hdom : Primrec (fun p : P => WindowCode.domain (WindowCode.var p.1) p.2.2.1) :=
    negative_primitive.comp (less_primitive.comp hv
      (numeral_primitive.comp (toNat_primitive.comp (IntegerAlgorithms.Proof.negate_primitive.comp he))))
  have hclose : Primrec (fun p : P => WindowCode.close p.1 p.2.1 p.2.2.1 p.2.2.2.1) :=
    conjunction_primitive.comp hdom
      (conjunction_primitive.comp (hat.comp hpa hps)
        (hat.comp hps (multiply_primitive.comp hc hpa)))
  have hguard : Primrec (fun p : P => WindowCode.conjunction
      (WindowCode.close p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2) :=
    conjunction_primitive.comp hclose hp
  have hrepl : Primrec₂ (fun p : P => fun d : Nat => WindowCode.replacement p.2.1 p.2.2.1 d) :=
    shift_primitive.comp
      (add_primitive.comp (ha.comp Primrec.fst) (numeral_primitive.comp Primrec.snd))
      (IntegerAlgorithms.Proof.negate_primitive.comp (he.comp Primrec.fst))
  have hbranch : Computable₂ (fun p : P => fun d : Nat =>
      WindowCode.matrixSubstitute p.1 (WindowCode.replacement p.2.1 p.2.2.1 d)
        (WindowCode.conjunction (WindowCode.close p.1 p.2.1 p.2.2.1 p.2.2.2.1) p.2.2.2.2)) :=
    matrix_computable.comp ((hguard.to_comp.comp Computable.fst).pair
      ((hi.to_comp.comp Computable.fst).pair hrepl.to_comp))
  have hlist : Computable (fun p : P => List.range (p.2.2.2.1 + 1)) :=
    Primrec.list_range.to_comp.comp (Primrec.nat_add.comp hc (Primrec.const 1)).to_comp
  exact any_primitive.to_comp.comp (map_computable hlist hbranch)

theorem actualCodeComputation : WindowCodeTargets.ActualCodeComputation :=
  ⟨term_computable, matrix_computable, finite_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.WindowCodeProof
