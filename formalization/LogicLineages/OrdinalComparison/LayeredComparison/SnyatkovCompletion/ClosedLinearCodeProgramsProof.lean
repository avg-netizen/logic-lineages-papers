module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearProof
open ClosedLinear
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem isEmpty_primitive {α : Type*} [Primcodable α] : Primrec (@List.isEmpty α) := by
  apply ((Primrec.eq.comp Primrec.list_length (Primrec.const 0)).decide).of_eq
  intro xs
  cases xs <;> rfl

theorem constantMatrix_primitive : Primrec Code.constantMatrix := by
  have hp : Primrec₂ (fun (_ : Unit) a => (LinearRows.Code.decodeAtom a).2.2.2.isEmpty) :=
    isEmpty_primitive.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp
      (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd))))
  exact (LinearRowsCodeProof.listAll_primitive hp).comp
    (Primrec.const ()) LinearRowsCodeProof.atoms_primitive

private theorem nonnegative_primitive : Primrec (fun z : Int => decide (0 ≤ z)) := by
  apply (Primrec.ite
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const false) (Primrec.const true)).of_eq
  intro z
  cases z with
  | ofNat n => cases n <;> rfl
  | negSucc n => rfl

private theorem constantAtom_primitive : Primrec Code.constantAtom := by
  let A := NormalForm.Code.AtomData
  have hz : Primrec (fun a : A => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun a : A => a.2.1 + 1) :=
    Primrec.succ.comp (Primrec.fst.comp Primrec.snd)
  have hd : Primrec (fun a : A => decide (a.2.2.1.natAbs % (a.2.1 + 1) = 0)) :=
    (Primrec.eq.comp
      (Primrec.nat_mod.comp (IntegerAlgorithms.Proof.abs_primitive.comp hz) hm)
      (Primrec.const 0)).decide
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (nonnegative_primitive.comp hz) hd

private def children (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

private theorem children_decreasing : ∀ code child, child ∈ children code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [children, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold children at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

private def assemble (code : Nat) (values : List Bool) : Bool :=
  if code % 6 = 0 then true
  else if code % 6 = 1 then false
  else if code % 6 = 2 then Code.constantAtom (LinearRows.Code.decodeAtom (code / 6))
  else if code % 6 = 3 then !values.getD 0 false
  else if code % 6 = 4 then values.getD 0 false && values.getD 1 false
  else values.getD 0 false || values.getD 1 false

private theorem evaluateConstants_equation (code : Nat) :
    Code.evaluateConstants code = assemble code ((children code).map Code.evaluateConstants) := by
  rw [Code.evaluateConstants]
  split_ifs <;> simp_all [children, assemble]

private theorem tag_primitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)
private theorem quotient_primitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)
private theorem tag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 6 = n) :=
  Primrec.eq.comp tag_primitive (Primrec.const n)
private theorem left_primitive : Primrec (fun code : Nat => (code / 6).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp quotient_primitive)
private theorem right_primitive : Primrec (fun code : Nat => (code / 6).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp quotient_primitive)
private theorem children_primitive : Primrec children :=
  Primrec.ite ((tag_is 0).or ((tag_is 1).or (tag_is 2))) (Primrec.const [])
    (Primrec.ite (tag_is 3)
      (Primrec.list_cons.comp quotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp left_primitive
        (Primrec.list_cons.comp right_primitive (Primrec.const []))))

private theorem assemble_primitive : Primrec₂ assemble := by
  let A := Nat × List Bool
  have h0 : Primrec (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).comp Primrec.snd (Primrec.const 1)
  have ha : Primrec (fun p : A => Code.constantAtom (LinearRows.Code.decodeAtom (p.1 / 6))) :=
    constantAtom_primitive.comp
      (LinearRowsCodeProof.decodeAtom_primitive.comp (quotient_primitive.comp Primrec.fst))
  exact Primrec.ite ((tag_is 0).comp Primrec.fst) (Primrec.const true)
    (Primrec.ite ((tag_is 1).comp Primrec.fst) (Primrec.const false)
      (Primrec.ite ((tag_is 2).comp Primrec.fst) ha
        (Primrec.ite ((tag_is 3).comp Primrec.fst) (Primrec.not.comp h0)
          (Primrec.ite ((tag_is 4).comp Primrec.fst) (Primrec.and.comp h0 h1)
            (Primrec.or.comp h0 h1)))))

private def step (values : List Bool) : Option Bool :=
  some (assemble values.length ((children values.length).map (fun i => values.getD i false)))

private theorem step_primitive : Primrec step := by
  have hs : Primrec (fun p : List Bool × Nat => p.1.getD p.2 false) :=
    (Primrec.list_getD false).comp Primrec.fst Primrec.snd
  have hm : Primrec (fun values : List Bool =>
      (children values.length).map (fun i => values.getD i false)) :=
    Primrec.list_map (children_primitive.comp Primrec.list_length) hs.to₂
  exact Primrec.option_some.comp (assemble_primitive.comp Primrec.list_length hm)

theorem evaluateConstants_primitive : Primrec Code.evaluateConstants := by
  have h : Primrec₂ (fun (_ : Unit) code => Code.evaluateConstants code) := by
    apply Primrec.nat_strong_rec _ (step_primitive.comp Primrec.snd).to₂
    intro _ code
    unfold step
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [evaluateConstants_equation code]
    apply congrArg (assemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := children_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id

theorem decideClosed_primitive : Primrec Code.decideClosed := by
  have htest : Primrec (fun code : Nat =>
      QuantifiedLinear.Code.admissible code && Code.constantMatrix (QuantifiedLinear.Code.eliminate code)) :=
    Primrec.and.comp QuantifiedLinearProof.admissible_primitive
      (constantMatrix_primitive.comp QuantifiedLinearProof.eliminate_primitive)
  exact Primrec.ite (Primrec.eq.comp htest (Primrec.const true))
    (Primrec.option_some.comp
      (evaluateConstants_primitive.comp QuantifiedLinearProof.eliminate_primitive))
    (Primrec.const none)

theorem actualNumericPrograms : ClosedLinearTargets.ActualNumericPrograms :=
  ⟨constantMatrix_primitive, evaluateConstants_primitive, decideClosed_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearProof
