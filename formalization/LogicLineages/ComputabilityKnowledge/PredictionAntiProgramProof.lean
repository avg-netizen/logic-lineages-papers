module

public import LogicLineages.ComputabilityKnowledge.Comparators.PredictionAntiProgram
public import Mathlib.Computability.PartrecCode

@[expose] public section

/-!
# A genuine uniform ordinary anti-predictor program (paper 14, `lem:finitevalues`)

Proves the frozen `Comparators.PredictionAntiProgram.Target`. The partial prefix
recursion and the length-only anti-program are partial recursive by
`Partrec.nat_rec`, `Partrec.bind` and `Partrec.optionCasesOn_right`. A fixed
universal code for the unpaired program is obtained from `Code.exists_code`;
its s-m-n curry is computable by `primrec₂_curry` and has the exact semantics by
`eval_curry`. Under the total-binary promise the partial computations return the
policy moves, so the compiled program is total binary and its selected policy is
the accepted semantic `antiEvader`.
-/

namespace LogicLineages.ComputabilityKnowledge.PredictionAntiProgramProof

open LogicLineages.ComputabilityKnowledge.PredictionGame
open LogicLineages.ComputabilityKnowledge.PredictionLearning
open LogicLineages.ComputabilityKnowledge.PredictionAntiProgram
open LogicLineages.ComputabilityKnowledge.Comparators.PredictionAntiProgram

theorem decode_bitValue (b : Bool) : decodeBit (bitValue b) = some b := by
  cases b <;> rfl

theorem bitValue_inj {a b : Bool} (h : bitValue a = bitValue b) : a = b := by
  cases a <;> cases b
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · rfl

/-! ## Partial recursiveness of the frozen partial computations -/

theorem pr_decodeBit : Primrec decodeBit := by
  have h0 : PrimrecPred (fun n : Nat => n = 0) := Primrec.eq.comp Primrec.id (Primrec.const 0)
  have h1 : PrimrecPred (fun n : Nat => n = 1) := Primrec.eq.comp Primrec.id (Primrec.const 1)
  refine Primrec.of_eq (Primrec.ite h0 (Primrec.const (some false))
    (Primrec.ite h1 (Primrec.const (some true)) (Primrec.const none))) ?_
  intro n
  rfl

theorem partrec_move : Partrec₂ partialMove := by
  have hev : Partrec (fun x : Code × List Bool =>
      Nat.Partrec.Code.eval x.1 (Encodable.encode x.2)) :=
    Nat.Partrec.Code.eval_part.comp Computable.fst (Computable.encode.comp Computable.snd)
  have hdec : Partrec₂ (fun (_ : Code × List Bool) (n : Nat) => Part.ofOption (decodeBit n)) :=
    Computable.ofOption (pr_decodeBit.to_comp.comp Computable.snd)
  refine Partrec.of_eq (Partrec.bind hev hdec) ?_
  intro x
  rfl

theorem prefix_rec (p : Code) (n : Nat) :
    Nat.rec (motive := fun _ => Part (List Bool)) (Part.some [])
      (fun _ IH => IH.bind fun i => (partialMove p i).bind fun b => Part.some (i ++ [!b])) n =
      partialAntiPrefix p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      exact congrArg
        (fun o => o.bind fun i => (partialMove p i).bind fun b => Part.some (i ++ [!b])) ih

theorem partrec_prefix : Partrec (fun x : Code × Nat => partialAntiPrefix x.1 x.2) := by
  have hcat : Computable₂ (fun (r : (Code × Nat) × (Nat × List Bool)) (b : Bool) =>
      r.2.2 ++ [!b]) :=
    (Primrec.list_concat.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
      (Primrec.not.comp Primrec.snd)).to_comp
  have hh : Partrec₂ (fun (a : Code × Nat) (q : Nat × List Bool) =>
      (partialMove a.1 q.2).bind fun b => Part.some (q.2 ++ [!b])) :=
    Partrec.bind (partrec_move.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.snd)) hcat.partrec₂
  refine Partrec.of_eq (Partrec.nat_rec Computable.snd
    (Computable.const ([] : List Bool)).partrec hh) ?_
  intro x
  exact prefix_rec x.1 x.2

theorem partrec_anti : Partrec (fun x : Code × Nat => antiProgram x.1 x.2) := by
  have hpre : Partrec (fun s : (Code × Nat) × List Bool =>
      partialAntiPrefix s.1.1 s.2.length) :=
    partrec_prefix.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.list_length.comp Computable.snd))
  have hbit : Computable₂ (fun (_ : ((Code × Nat) × List Bool) × List Bool) (b : Bool) =>
      bitValue (!b)) :=
    ((Primrec.dom_bool (fun b : Bool => bitValue (!b))).comp Primrec.snd).to_comp
  have hlast : Partrec₂ (fun (s : (Code × Nat) × List Bool) (xs : List Bool) =>
      (partialMove s.1.1 xs).bind fun b => Part.some (bitValue (!b))) :=
    Partrec.bind (partrec_move.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      Computable.snd) hbit.partrec₂
  have hcore : Partrec₂ (fun (x : Code × Nat) (h : List Bool) =>
      (partialAntiPrefix x.1 h.length).bind fun xs =>
        (partialMove x.1 xs).bind fun b => Part.some (bitValue (!b))) :=
    Partrec.bind hpre hlast
  have ho : Computable (fun x : Code × Nat => Encodable.decode (α := List Bool) x.2) :=
    Computable.decode.comp Computable.snd
  refine Partrec.of_eq (Partrec.optionCasesOn_right ho (Computable.const 0) hcore) ?_
  intro x
  unfold antiProgram
  cases Encodable.decode (α := List Bool) x.2 <;> rfl

/-! ## A fixed universal code and its uniform s-m-n compiler -/

theorem partrec_unpaired : Partrec (fun m : Nat =>
    antiProgram (Denumerable.ofNat Code m.unpair.1) m.unpair.2) :=
  partrec_anti.comp
    (((Computable.ofNat Code).comp (Computable.fst.comp Primrec.unpair.to_comp)).pair
      (Computable.snd.comp Primrec.unpair.to_comp))

theorem code_semantics (c : Code)
    (hc : Nat.Partrec.Code.eval c =
      fun m => antiProgram (Denumerable.ofNat Code m.unpair.1) m.unpair.2) :
    CodeSemantics c := by
  intro p input
  have h1 : (Nat.pair (Encodable.encode p) input).unpair.1 = Encodable.encode p :=
    congrArg Prod.fst (Nat.unpair_pair _ _)
  have h2 : (Nat.pair (Encodable.encode p) input).unpair.2 = input :=
    congrArg Prod.snd (Nat.unpair_pair _ _)
  show Nat.Partrec.Code.eval (Nat.Partrec.Code.curry c (Encodable.encode p)) input = _
  rw [Nat.Partrec.Code.eval_curry, hc]
  show antiProgram (Denumerable.ofNat Code (Nat.pair (Encodable.encode p) input).unpair.1)
    (Nat.pair (Encodable.encode p) input).unpair.2 = antiProgram p input
  rw [h1, h2, Denumerable.ofNat_encode]

theorem compiled_computable (c : Code) : Computable (compiledAnti c) := by
  have h : Primrec (fun p : Code => Nat.Partrec.Code.curry c (Encodable.encode p)) :=
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const c) Primrec.encode
  exact h.to_comp.of_eq fun p => rfl

/-! ## Behaviour on total-binary predictors -/

theorem move_total (p : Code) (hp : TotalBinary p) (h : List Bool) :
    partialMove p h = Part.some (policy p hp h) := by
  have hs : Nat.Partrec.Code.eval p (Encodable.encode h) =
      Part.some (bitValue (policy p hp h)) :=
    Part.eq_some_iff.mpr (Classical.choose_spec (hp h))
  show (Nat.Partrec.Code.eval p (Encodable.encode h)).bind
    (fun n => Part.ofOption (decodeBit n)) = _
  rw [hs, Part.bind_some, decode_bitValue, Part.coe_some]

theorem prefix_total (p : Code) (hp : TotalBinary p) (n : Nat) :
    partialAntiPrefix p n = Part.some (antiPrefix (policy p hp) n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      show (partialAntiPrefix p n).bind
          (fun h => (partialMove p h).bind fun b => Part.some (h ++ [!b])) =
        Part.some (antiPrefix (policy p hp) n ++ [!(policy p hp (antiPrefix (policy p hp) n))])
      rw [ih, Part.bind_some, move_total p hp, Part.bind_some]

theorem anti_value (p : Code) (hp : TotalBinary p) (h : List Bool) :
    antiProgram p (Encodable.encode h) = Part.some (bitValue (antiEvader (policy p hp) h)) := by
  unfold antiProgram
  rw [Encodable.encodek]
  show (partialAntiPrefix p h.length).bind
      (fun xs => (partialMove p xs).bind fun b => Part.some (bitValue (!b))) =
    Part.some (bitValue (!(policy p hp (antiPrefix (policy p hp) h.length))))
  rw [prefix_total p hp, Part.bind_some, move_total p hp, Part.bind_some]

theorem compiled_total (c : Code) (hc : CodeSemantics c) (p : Code) (hp : TotalBinary p) :
    TotalBinary (compiledAnti c p) := by
  intro h
  refine ⟨antiEvader (policy p hp) h, ?_⟩
  rw [hc p (Encodable.encode h), anti_value p hp h]
  exact Part.mem_some _

theorem compiled_policy (c : Code) (hc : CodeSemantics c) (p : Code) (hp : TotalBinary p)
    (he : TotalBinary (compiledAnti c p)) :
    policy (compiledAnti c p) he = antiEvader (policy p hp) := by
  funext h
  have hs : bitValue (policy (compiledAnti c p) he h) ∈
      Nat.Partrec.Code.eval (compiledAnti c p) (Encodable.encode h) :=
    Classical.choose_spec (he h)
  have hv : bitValue (policy (compiledAnti c p) he h) ∈
      Part.some (bitValue (antiEvader (policy p hp) h)) :=
    Eq.mp (congrArg (fun value : Part Nat =>
      bitValue (policy (compiledAnti c p) he h) ∈ value)
      ((hc p (Encodable.encode h)).trans (anti_value p hp h))) hs
  exact bitValue_inj (Part.mem_some_iff.mp hv)

theorem uniformCompiler : UniformAntiCompiler := by
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp partrec_unpaired)
  have hsem := code_semantics c hc
  refine ⟨c, compiled_computable c, hsem, fun p hp => ?_⟩
  have he := compiled_total c hsem p hp
  have hpol := compiled_policy c hsem p hp he
  refine ⟨he, hpol, fun n => ?_, ?_⟩
  · rw [hpol]
    exact anti_disagrees (policy p hp) n
  · rw [hpol]
    exact anti_not_learned (policy p hp)

theorem uniformAntiProgram :
    LogicLineages.ComputabilityKnowledge.Comparators.PredictionAntiProgram.Target := by
  exact ⟨partrec_prefix, partrec_anti, uniformCompiler⟩

end LogicLineages.ComputabilityKnowledge.PredictionAntiProgramProof
