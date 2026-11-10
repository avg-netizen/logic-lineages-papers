module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeFormulaProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
open PlainBlockLinearizationCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

def linearizeChildren (code : Nat) : List Nat :=
  if code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2 then []
  else if code % 6 = 3 then [code / 6]
  else [(code / 6).unpair.1, (code / 6).unpair.2]

theorem linearizeChildren_decreasing : ∀ code child, child ∈ linearizeChildren code → child < code := by
  intro code child h
  by_cases hleaf : code % 6 = 0 ∨ code % 6 = 1 ∨ code % 6 = 2
  · simp [linearizeChildren, hleaf] at h
  have hpos : 0 < code := by omega
  have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
  have hl := Nat.unpair_left_le (code / 6)
  have hr := Nat.unpair_right_le (code / 6)
  unfold linearizeChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega
#print axioms linearizeChildren_decreasing

theorem linearizeTag_primitive : Primrec (fun code : Nat => code % 6) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 6)
#print axioms linearizeTag_primitive

theorem linearizeQuotient_primitive : Primrec (fun code : Nat => code / 6) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 6)
#print axioms linearizeQuotient_primitive

theorem linearizeTag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 6 = n) :=
  Primrec.eq.comp linearizeTag_primitive (Primrec.const n)
#print axioms linearizeTag_is

theorem linearizeLeft_primitive : Primrec (fun code : Nat => (code / 6).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp linearizeQuotient_primitive)
#print axioms linearizeLeft_primitive

theorem linearizeRight_primitive : Primrec (fun code : Nat => (code / 6).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp linearizeQuotient_primitive)
#print axioms linearizeRight_primitive

theorem linearizeChildren_primitive : Primrec linearizeChildren :=
  Primrec.ite ((linearizeTag_is 0).or ((linearizeTag_is 1).or (linearizeTag_is 2))) (Primrec.const [])
    (Primrec.ite (linearizeTag_is 3)
      (Primrec.list_cons.comp linearizeQuotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp linearizeLeft_primitive
        (Primrec.list_cons.comp linearizeRight_primitive (Primrec.const []))))

def linearizeAssemble (args : Nat)
    (code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then linearizeAtom args (BlockFormulaSubstitutionCode.decodeAtom (code / 6))
  else if code % 6 = 3 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + code % 6
#print axioms linearizeChildren_primitive

theorem linearize_equation (args : Nat) (code : Nat) :
    linearize args code =
      linearizeAssemble args code ((linearizeChildren code).map (linearize args)) := by
  rw [linearize]
  split_ifs <;> simp_all [linearizeChildren, linearizeAssemble]
#print axioms linearize_equation

theorem linearizeAssemble_primitive :
    Primrec (fun p : Nat × (Nat × List Nat) => linearizeAssemble p.1 p.2.1 p.2.2) := by
  let A := Nat × (Nat × List Nat)
  have hc : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have h0 : Primrec (fun p : A => p.2.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp hv (Primrec.const 1)
  have hatom : Primrec (fun p : A => linearizeAtom p.1 (BlockFormulaSubstitutionCode.decodeAtom (p.2.1 / 6))) :=
    linearizeAtom_primitive.comp Primrec.fst
      (BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp (linearizeQuotient_primitive.comp hc))
  have hb : Primrec (fun p : A =>
      6 * Nat.pair (p.2.2.getD 0 0) (p.2.2.getD 1 0) + p.2.1 % 6) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp h0 h1))
      (linearizeTag_primitive.comp hc)
  exact Primrec.ite ((linearizeTag_is 0).comp hc) (Primrec.const 0)
    (Primrec.ite ((linearizeTag_is 1).comp hc) (Primrec.const 1)
      (Primrec.ite ((linearizeTag_is 2).comp hc) hatom
        (Primrec.ite ((linearizeTag_is 3).comp hc) ((unary_primitive 6 3).comp h0) hb)))

def linearizeStep (args : Nat)
    (values : List Nat) : Option Nat :=
  some (linearizeAssemble args values.length
    ((linearizeChildren values.length).map (fun i => values.getD i 0)))
#print axioms linearizeAssemble_primitive

theorem linearizeStep_primitive : Primrec₂ (linearizeStep) := by
  let A := Nat × List Nat
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (linearizeChildren p.2.length).map (fun i => p.2.getD i 0)) :=
    Primrec.list_map
      (linearizeChildren_primitive.comp (Primrec.list_length.comp Primrec.snd)) hs.to₂
  have hp : Primrec (fun p : A =>
      (p.1, p.2.length, (linearizeChildren p.2.length).map (fun i => p.2.getD i 0))) :=
    Primrec.fst.pair ((Primrec.list_length.comp Primrec.snd).pair hm)
  exact Primrec.option_some.comp (linearizeAssemble_primitive.comp hp)

#print axioms linearizeStep_primitive

/-- Actual strong recursion for the frozen whole-formula atom replacement,
using the internally proved concrete row program. -/

theorem linearize_primitive : Primrec₂ (fun args code => linearize args code) := by
  apply Primrec.nat_strong_rec _ linearizeStep_primitive
  intro args code
  unfold linearizeStep
  simp only [List.length_map, List.length_range]
  apply congrArg some
  rw [linearize_equation args code]
  apply congrArg (linearizeAssemble args code)
  apply List.map_congr_left
  intro i hi
  have hlt := linearizeChildren_decreasing code i hi
  simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
#print axioms linearize_primitive

theorem actualFormulaPrograms : PlainBlockLinearizationCodeTargets.ActualFormulaPrograms :=
  ⟨cutoff_primitive.to_comp, frame_primitive.to_comp, outside_primitive.to_comp, linearize_primitive.to_comp⟩
#print axioms actualFormulaPrograms

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
