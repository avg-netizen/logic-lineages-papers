module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationProof
open Turing PredictionFiniteSerialization PredictionFiniteSerializationTargets

private theorem pr_action (a : Nat) : Primrec (@numericAction a) := by
  exact (Primrec.sumCasesOn Primrec.id
    (Primrec.sumInl.comp Primrec.snd).to₂
    (Primrec.sumInr.comp (Primrec.fin_val.comp Primrec.snd)).to₂).of_eq
    (fun x => by cases x <;> rfl)

private theorem pr_entry (q a : Nat) : Primrec (@numericEntry q a) :=
  (Primrec.fin_val.comp Primrec.fst).pair ((pr_action a).comp Primrec.snd)

theorem effectiveFixedDimensionSerializer : EffectiveFixedDimensionSerializer := by
  intro q a
  have hr : Primrec (fun z : Fin (q + 1) × FinMachine q a => rows z.2) := by
    apply Primrec.list_ofFn
    intro i
    have hm : Primrec (fun z : Fin (q + 1) × FinMachine q a => z.2 i.divNat i.modNat) :=
      Primrec.fin_app.comp
        (Primrec.fin_app.comp Primrec.snd (Primrec.const i.divNat)) (Primrec.const i.modNat)
    exact Primrec.option_map hm ((pr_entry q a).comp Primrec.snd).to₂
  exact Primrec.encode.comp ((Primrec.const a).pair
    ((Primrec.fin_val.comp Primrec.fst).pair hr))

theorem exactNumericLayout : ExactNumericLayout := by
  intro q a start m
  exact ⟨rfl, rfl, List.length_ofFn⟩

theorem exactTransitionLookup : ExactTransitionLookup := by
  intro q a start m s b
  let i : Fin ((q + 1) * (a + 3)) := finProdFinEquiv (s, b)
  have hi : i.val = s.val * (a + 3) + b.val := by
    simp [i, finProdFinEquiv, Nat.mul_comm, Nat.add_comm]
  have hr : i.divNat = s := congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (s, b))
  have hc : i.modNat = b := congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (s, b))
  have hg : (rows m)[i.val]? = some ((m i.divNat i.modNat).map numericEntry) := by
    simp only [rows, List.getElem?_ofFn, dif_pos i.isLt]
  change ((rows m)[s.val * (a + 3) + b.val % (a + 3)]?).bind id = _
  rw [Nat.mod_eq_of_lt b.isLt, ← hi, hg]
  simp [hr, hc]

private theorem action_agrees {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a)
    (act : FinAction a) :
    PredictionFiniteAlphabet.actionStmt (table start m) (numericAction act) = finiteStmt act := by
  cases act with
  | inl b => cases b <;> rfl
  | inr s =>
    change TM0.Stmt.write (PredictionFiniteAlphabet.symbol (table start m) s.val) = TM0.Stmt.write s
    congr 1
    apply Fin.ext
    exact Nat.mod_eq_of_lt s.isLt

private theorem machine_agrees {q a : Nat} (start : Fin (q + 1)) (m : FinMachine q a)
    (s : Fin (q + 1)) (b : Fin (a + 3)) :
    PredictionFiniteAlphabet.machine (table start m) s.val b =
      (finiteMachine m s b).map (fun x => (x.1.val, x.2)) := by
  unfold PredictionFiniteAlphabet.machine finiteMachine
  rw [exactTransitionLookup q a start m s b]
  try simp only [Option.map_map]
  congr 1
  funext x
  change (x.1.val, PredictionFiniteAlphabet.actionStmt (table start m) (numericAction x.2)) =
    (x.1.val, finiteStmt x.2)
  exact congrArg (fun act => (x.1.val, act)) (action_agrees start m x.2)

theorem exactSerializedStep : ExactSerializedStep := by
  intro q a start m c
  rcases c with ⟨s, tape⟩
  simp only [TM0.step, embedCfg]
  rw [machine_agrees]
  cases h : finiteMachine m s tape.head with
  | none => rfl
  | some x => rcases x with ⟨s', act⟩; cases act <;> rfl

end LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationProof
