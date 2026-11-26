module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationTermProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem computable_ite {α β : Type} [Primcodable α] [Primcodable β]
    {c : α → Prop} [DecidablePred c] {f g : α → β}
    (hc : PrimrecPred c) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if c a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hc.decide.to_comp hf hg

def matrixChildren (code : Nat) : List Nat :=
  if code % 8 < 5 then [] else if code % 8 = 5 then [code / 8]
  else [(code / 8).unpair.1, (code / 8).unpair.2]

theorem matrixTag_primitive : Primrec (fun code : Nat => code % 8) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
theorem matrixQuotient_primitive : Primrec (fun code : Nat => code / 8) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 8)
theorem matrixLeft_primitive : Primrec (fun code : Nat => (code / 8).unpair.1) :=
  Primrec.fst.comp (Primrec.unpair.comp matrixQuotient_primitive)
theorem matrixRight_primitive : Primrec (fun code : Nat => (code / 8).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp matrixQuotient_primitive)
theorem matrixTag_is (n : Nat) : PrimrecPred (fun code : Nat => code % 8 = n) :=
  Primrec.eq.comp matrixTag_primitive (Primrec.const n)
theorem matrixChildren_primitive : Primrec matrixChildren :=
  Primrec.ite (Primrec.nat_lt.comp matrixTag_primitive (Primrec.const 5)) (Primrec.const [])
    (Primrec.ite (matrixTag_is 5)
      (Primrec.list_cons.comp matrixQuotient_primitive (Primrec.const []))
      (Primrec.list_cons.comp matrixLeft_primitive
        (Primrec.list_cons.comp matrixRight_primitive (Primrec.const []))))

theorem matrixChildren_decreasing : ∀ code child : Nat,
    child ∈ matrixChildren code → child < code := by
  intro code child h
  have hm : code % 8 < 8 := Nat.mod_lt _ (by decide)
  by_cases hleaf : code % 8 < 5
  · simp [matrixChildren, hleaf] at h
  have hp : 0 < code := by omega
  have hd : code / 8 < code := Nat.div_lt_self hp (by decide)
  have hl := Nat.unpair_left_le (code / 8)
  have hr := Nat.unpair_right_le (code / 8)
  unfold matrixChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals omega

def matrixVariablesAssemble (code : Nat) (values : List (List Nat)) : List Nat :=
  if code % 8 = 0 ∨ code % 8 = 1 then []
  else if code % 8 = 2 ∨ code % 8 = 3 then
    Code.termVariables (code / 8).unpair.1 ++ Code.termVariables (code / 8).unpair.2
  else if code % 8 = 4 then Code.termVariables (code / 8).unpair.2
  else if code % 8 = 5 then values.getD 0 []
  else values.getD 0 [] ++ values.getD 1 []

theorem matrixVariablesAssemble_computable : Computable₂ matrixVariablesAssemble := by
  let A := Nat × List (List Nat)
  have h0 : Computable (fun p : A => p.2.getD 0 []) :=
    (Primrec.list_getD ([] : List Nat)).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 []) :=
    (Primrec.list_getD ([] : List Nat)).to_comp.comp Computable.snd (Computable.const 1)
  have hl : Computable (fun p : A => Code.termVariables (p.1 / 8).unpair.1) :=
    termVariables_computable.comp (matrixLeft_primitive.to_comp.comp Computable.fst)
  have hr : Computable (fun p : A => Code.termVariables (p.1 / 8).unpair.2) :=
    termVariables_computable.comp (matrixRight_primitive.to_comp.comp Computable.fst)
  exact computable_ite (((matrixTag_is 0).or (matrixTag_is 1)).comp Primrec.fst) (Computable.const [])
    (computable_ite (((matrixTag_is 2).or (matrixTag_is 3)).comp Primrec.fst)
      (Primrec.list_append.to_comp.comp hl hr)
      (computable_ite ((matrixTag_is 4).comp Primrec.fst) hr
        (computable_ite ((matrixTag_is 5).comp Primrec.fst) h0
          (Primrec.list_append.to_comp.comp h0 h1))))

theorem matrixVariables_equation (code : Nat) :
    Code.matrixVariables code = matrixVariablesAssemble code
      ((matrixChildren code).map Code.matrixVariables) := by
  have hm : code % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [Code.matrixVariables]
  unfold matrixVariablesAssemble matrixChildren
  split_ifs <;> simp_all <;> omega

theorem matrixVariables_computable : Computable Code.matrixVariables := by
  classical
  exact (LayeredComparison.FiniteGraph.Proof.exactDecreasingGraph Nat (List Nat) matrixChildren matrixVariablesAssemble id
    matrixChildren_primitive.to_comp matrixVariablesAssemble_computable Computable.id
    Code.matrixVariables matrixChildren_decreasing matrixVariables_equation).2

def forestAssemble (code : Nat) (values : List Nat) : Nat :=
  if code % 8 = 0 ∨ code % 8 = 1 then 0
  else if code % 8 = 2 ∨ code % 8 = 3 then 10 * (code / 8) + 2
  else if code % 8 = 4 then (code / 8).unpair.2
  else if code % 8 = 5 then values.getD 0 0
  else 10 * Nat.pair (values.getD 0 0) (values.getD 1 0) + 2

theorem forestAssemble_primitive : Primrec₂ forestAssemble := by
  let A := Nat × List Nat
  have h0 : Primrec (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 1)
  exact Primrec.ite (((matrixTag_is 0).or (matrixTag_is 1)).comp Primrec.fst) (Primrec.const 0)
    (Primrec.ite (((matrixTag_is 2).or (matrixTag_is 3)).comp Primrec.fst)
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10)
        (matrixQuotient_primitive.comp Primrec.fst)) (Primrec.const 2))
      (Primrec.ite ((matrixTag_is 4).comp Primrec.fst) (matrixRight_primitive.comp Primrec.fst)
        (Primrec.ite ((matrixTag_is 5).comp Primrec.fst) h0
          (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 10)
            (Primrec₂.natPair.comp h0 h1)) (Primrec.const 2)))))

theorem forest_equation (code : Nat) :
    Code.forest code = forestAssemble code ((matrixChildren code).map Code.forest) := by
  have hm : code % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [Code.forest]
  unfold forestAssemble matrixChildren
  split_ifs <;> simp_all <;> omega

theorem forest_computable : Computable Code.forest := by
  classical
  exact (LayeredComparison.FiniteGraph.Proof.exactDecreasingGraph Nat Nat matrixChildren forestAssemble id
    matrixChildren_primitive.to_comp forestAssemble_primitive.to_comp Computable.id
    Code.forest matrixChildren_decreasing forest_equation).2
end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
