module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeRowProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
open PlainBlockProjectionCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

def formulaAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 6 = 0 then 0
  else if code % 6 = 1 then 1
  else if code % 6 = 2 then atom (BlockFormulaSubstitutionCode.decodeAtom (code / 6))
  else if code % 6 = 3 then WindowCode.negative (values.getD 0 0)
  else 8 * Nat.pair (values.getD 0 0) (values.getD 1 0) + (code % 6 + 2)

theorem formula_equation (code : Nat) :
    formula code = formulaAssemble code
      ((PlainBlockLinearizationCodeProof.linearizeChildren code).map formula) := by
  rw [formula]
  split_ifs <;> simp_all [PlainBlockLinearizationCodeProof.linearizeChildren, formulaAssemble, WindowCode.negative]
#print axioms formula_equation

attribute [local irreducible] atom

theorem formulaAssemble_primitive : Primrec₂ formulaAssemble := by
  let A := Nat × List Nat
  have h0 : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  have ha : Primrec (fun p : A => atom (BlockFormulaSubstitutionCode.decodeAtom (p.1 / 6))) :=
    atom_primitive.comp (BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp
      (PlainBlockLinearizationCodeProof.linearizeQuotient_primitive.comp Primrec.fst))
  have hb : Primrec (fun p : A => 8 * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + (p.1 % 6 + 2)) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp h0 h1))
      (Primrec.nat_add.comp (PlainBlockLinearizationCodeProof.linearizeTag_primitive.comp Primrec.fst) (Primrec.const 2))
  exact Primrec.ite ((PlainBlockLinearizationCodeProof.linearizeTag_is 0).comp Primrec.fst) (Primrec.const 0)
    (Primrec.ite ((PlainBlockLinearizationCodeProof.linearizeTag_is 1).comp Primrec.fst) (Primrec.const 1)
      (Primrec.ite ((PlainBlockLinearizationCodeProof.linearizeTag_is 2).comp Primrec.fst) ha
        (Primrec.ite ((PlainBlockLinearizationCodeProof.linearizeTag_is 3).comp Primrec.fst)
          (negative_primitive.comp h0) hb)))
#print axioms formulaAssemble_primitive

def formulaStep (_ : Unit) (values : List Nat) : Option Nat :=
  some (formulaAssemble values.length
    ((PlainBlockLinearizationCodeProof.linearizeChildren values.length).map (fun i => values.getD i 0)))

theorem formulaStep_primitive : Primrec₂ formulaStep := by
  let A := Unit × List Nat
  have hs : Primrec (fun p : A × Nat => p.1.2.getD p.2 0) :=
    (Primrec.list_getD (0 : Nat)).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : A =>
      (PlainBlockLinearizationCodeProof.linearizeChildren p.2.length).map (fun i => p.2.getD i 0)) :=
    Primrec.list_map (PlainBlockLinearizationCodeProof.linearizeChildren_primitive.comp
      (Primrec.list_length.comp Primrec.snd)) hs.to₂
  exact Primrec.option_some.comp
    (formulaAssemble_primitive.comp (Primrec.list_length.comp Primrec.snd) hm)
#print axioms formulaStep_primitive

theorem formula_primitive : Primrec formula := by
  have h : Primrec₂ (fun (_ : Unit) (code : Nat) => formula code) := by
    apply Primrec.nat_strong_rec _ formulaStep_primitive
    intro args code
    unfold formulaStep
    simp only [List.length_map, List.length_range]
    apply congrArg some
    rw [formula_equation code]
    apply congrArg (formulaAssemble code)
    apply List.map_congr_left
    intro i hi
    have hlt := PlainBlockLinearizationCodeProof.linearizeChildren_decreasing code i hi
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt]
  exact h.comp (Primrec.const ()) Primrec.id
#print axioms formula_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockProjectionCodeProof
