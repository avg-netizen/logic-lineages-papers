module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
open BooleanSourceBlocks
attribute [local irreducible] Nat.sqrt Nat.unpair HomogeneousSource.Code.admissible HomogeneousSource.Code.decide

theorem combine_primitive : Primrec₂ combine := by
  let A := Option Bool × Option Bool
  have hm : Primrec₂ (fun p : A => fun x : Bool => p.2.map (fun y => x && y)) :=
    Primrec.option_map (Primrec.snd.comp Primrec.fst)
      (Primrec.and.comp (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂
  exact Primrec.option_bind Primrec.fst hm

private theorem not_primitive : Primrec (fun x : Option Bool => x.map Bool.not) :=
  Primrec.option_map Primrec.id (Primrec.not.comp Primrec.snd).to₂

private def stage (params : List Nat) (prior : List (Option Bool)) : Option (Option Bool) :=
  some (if HomogeneousSource.Code.admissible prior.length then HomogeneousSource.Code.decide params prior.length
    else if prior.length % 5 = 2 then (prior.getD (prior.length / 5) none).map Bool.not
    else if prior.length % 5 = 3 then combine (prior.getD (prior.length / 5).unpair.1 none)
      (prior.getD (prior.length / 5).unpair.2 none)
    else none)

private theorem stage_primitive : Primrec₂ stage := by
  let A := List Nat × List (Option Bool)
  have hn : Primrec (fun p : A => p.2.length) := Primrec.list_length.comp Primrec.snd
  have hq : Primrec (fun p : A => p.2.length / 5) := Primrec.nat_div.comp hn (Primrec.const 5)
  have ht : Primrec (fun p : A => p.2.length % 5) := Primrec.nat_mod.comp hn (Primrec.const 5)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hq)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hq)
  have hgetq := (Primrec.list_getD (none : Option Bool)).comp Primrec.snd hq
  have hgetl := (Primrec.list_getD (none : Option Bool)).comp Primrec.snd hl
  have hgetr := (Primrec.list_getD (none : Option Bool)).comp Primrec.snd hr
  have hadm : PrimrecPred (fun p : A => HomogeneousSource.Code.admissible p.2.length = true) :=
    Primrec.eq.comp (HomogeneousSourceProof.admissible_primitive.comp hn) (Primrec.const true)
  exact Primrec.option_some.comp (Primrec.ite hadm
    (HomogeneousSourceProof.decide_primitive.comp Primrec.fst hn)
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) (not_primitive.comp hgetq)
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3))
        (combine_primitive.comp hgetl hgetr) (Primrec.const none))))

theorem actualNumericProgram : BooleanSourceBlocksTargets.ActualNumericProgram := by
  apply Primrec.nat_strong_rec _ stage_primitive
  intro params code
  unfold stage
  simp only [List.length_map, List.length_range]
  rw [Code.decide]
  by_cases ha : HomogeneousSource.Code.admissible code = true
  · simp only [if_pos ha]
  · simp only [if_neg ha]
    by_cases h2 : code % 5 = 2
    · have hd : code / 5 < code := Nat.div_lt_self (by omega) (by decide)
      simp [h2, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd]
    · by_cases h3 : code % 5 = 3
      · have hd : code / 5 < code := Nat.div_lt_self (by omega) (by decide)
        have hl : (code / 5).unpair.1 < code := lt_of_le_of_lt (Nat.unpair_left_le _) hd
        have hr : (code / 5).unpair.2 < code := lt_of_le_of_lt (Nat.unpair_right_le _) hd
        simp [h2, h3, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hl, List.getElem?_range hr]
      · simp only [if_neg h2, if_neg h3]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BooleanSourceBlocksProof
