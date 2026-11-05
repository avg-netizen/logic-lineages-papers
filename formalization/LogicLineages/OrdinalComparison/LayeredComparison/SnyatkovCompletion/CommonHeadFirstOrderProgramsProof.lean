module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadExactVariablesProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderProgram
open CommonHeadFirstOrder

def children (code : Nat) : List Nat :=
  if code % 5 = 0 then []
  else if code % 5 = 1 then [code / 5]
  else if code % 5 = 2 then [(code / 5).unpair.1, (code / 5).unpair.2]
  else [(code / 5).unpair.2]
noncomputable def assemble (code : Nat) (xs : List Nat) : Nat :=
  if code % 5 = 0 then BaseBooleanSource.Code.compile (CommonHeadExactVariables.output (Code.atom (code / 5)))
  else if code % 5 = 1 then 5 * xs.getD 0 0 + 2
  else if code % 5 = 2 then 5 * Nat.pair (xs.getD 0 0) (xs.getD 1 0) + 3
  else if code % 5 = 3 then 5 * Nat.pair (code / 5).unpair.1 (xs.getD 0 0) + 4
  else 5 * Nat.pair (code / 5).unpair.1
    (5 * Nat.pair (Code.positiveGuard (code / 5).unpair.1) (xs.getD 0 0) + 3) + 4

theorem decreasing (code child : Nat) (h : child ∈ children code) : child < code := by
  have hl := Nat.unpair_left_le (code / 5)
  have hr := Nat.unpair_right_le (code / 5)
  unfold children at h
  split_ifs at h with h0 h1 h2
  · simp at h
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    omega

theorem equation (code : Nat) : Code.translate code =
    assemble code ((children code).map Code.translate) := by
  rw [Code.translate]
  unfold assemble children
  split_ifs <;> simp

attribute [local irreducible] Nat.sqrt Nat.unpair

theorem atom_primitive : Primrec Code.atom :=
  Primrec.option_getD.comp (Primrec.decode : Primrec (fun n : Nat =>
    (Encodable.decode n : Option CommonHeadExactVariables.Input))) (Primrec.const ([], 0, 0, 0))

theorem positive_primitive : Primrec Code.positiveGuard :=
  (SourceBooleanProgramsProof.binary_primitive 5 1).comp (Primrec.const 0)
    ((SourceBooleanProgramsProof.unary_primitive 4 1).comp Primrec.id)

theorem tag : Primrec (fun n : Nat => n % 5) := Primrec.nat_mod.comp Primrec.id (Primrec.const 5)
theorem quotient : Primrec (fun n : Nat => n / 5) := Primrec.nat_div.comp Primrec.id (Primrec.const 5)
theorem left : Primrec (fun n : Nat => (n / 5).unpair.1) := Primrec.fst.comp (Primrec.unpair.comp quotient)
theorem right : Primrec (fun n : Nat => (n / 5).unpair.2) := Primrec.snd.comp (Primrec.unpair.comp quotient)

theorem children_primitive : Primrec children :=
  Primrec.ite (Primrec.eq.comp tag (Primrec.const 0)) (Primrec.const [])
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1))
      (Primrec.list_cons.comp quotient (Primrec.const []))
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
        (Primrec.list_cons.comp left (Primrec.list_cons.comp right (Primrec.const [])))
        (Primrec.list_cons.comp right (Primrec.const []))))

private theorem computable_ite {A B : Type} [Primcodable A] [Primcodable B]
    {p : A → Prop} [DecidablePred p] {f g : A → B}
    (hp : Computable (fun a => decide (p a))) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  apply (Computable.cond hp hf hg).of_eq
  intro a
  by_cases h : p a <;> simp [h]

theorem assemble_computable : Computable₂ assemble := by
  let A := Nat × List Nat
  have ha : Computable (fun p : A => BaseBooleanSource.Code.compile
      (CommonHeadExactVariables.output (Code.atom (p.1 / 5)))) :=
    BaseBooleanSourceProof.compile_primitive.to_comp.comp
      (CommonHeadExactVariablesProof.actualOutputProgram.comp
        (atom_primitive.to_comp.comp (quotient.to_comp.comp Computable.fst)))
  have h0 : Primrec (fun p : A => p.2.getD 0 0) := (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0)
  have h1 : Primrec (fun p : A => p.2.getD 1 0) := (Primrec.list_getD 0).comp Primrec.snd (Primrec.const 1)
  have hn : Primrec (fun p : A => 5 * p.2.getD 0 0 + 2) :=
    (SourceBooleanProgramsProof.unary_primitive 5 2).comp h0
  have hc : Primrec (fun p : A => 5 * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + 3) :=
    (SourceBooleanProgramsProof.binary_primitive 5 3).comp h0 h1
  have he : Primrec (fun p : A => 5 * Nat.pair (p.1 / 5).unpair.1 (p.2.getD 0 0) + 4) :=
    (SourceBooleanProgramsProof.binary_primitive 5 4).comp (left.comp Primrec.fst) h0
  have hp : Primrec (fun p : A => 5 * Nat.pair (p.1 / 5).unpair.1
      (5 * Nat.pair (Code.positiveGuard (p.1 / 5).unpair.1) (p.2.getD 0 0) + 3) + 4) :=
    (SourceBooleanProgramsProof.binary_primitive 5 4).comp (left.comp Primrec.fst)
      ((SourceBooleanProgramsProof.binary_primitive 5 3).comp
        (positive_primitive.comp (left.comp Primrec.fst)) h0)
  exact computable_ite (Primrec.eq.comp (tag.comp Primrec.fst) (Primrec.const 0)).decide.to_comp ha
    (computable_ite (Primrec.eq.comp (tag.comp Primrec.fst) (Primrec.const 1)).decide.to_comp hn.to_comp
      (computable_ite (Primrec.eq.comp (tag.comp Primrec.fst) (Primrec.const 2)).decide.to_comp hc.to_comp
        (computable_ite (Primrec.eq.comp (tag.comp Primrec.fst) (Primrec.const 3)).decide.to_comp he.to_comp hp.to_comp)))

theorem actualNumericProgram : CommonHeadFirstOrderTargets.ActualNumericProgram :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph Nat Nat children assemble id
    children_primitive.to_comp assemble_computable Computable.id Code.translate decreasing equation).2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadFirstOrderProgram
