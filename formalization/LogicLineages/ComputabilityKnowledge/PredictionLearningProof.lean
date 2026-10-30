module

public import LogicLineages.ComputabilityKnowledge.Comparators.PredictionLearning
public import Mathlib.Computability.PartrecCode

@[expose] public section

/-!
# Proof of paper 14's recursive learning matrix (`lem:learning`)

Proves the frozen `Comparators.PredictionLearning.Target`. A successful bounded
move agrees with the actual policy by `evaln` soundness and uniqueness of the
partial output; bounded plays are then the actual source histories by induction.
Conversely `evaln` completeness and monotonicity give one common stage for any
finite actual play. The Boolean matrix is primitive recursive, built from
`primrec_evaln`, the binary decoder, option bind and natural recursion.
-/

namespace LogicLineages.ComputabilityKnowledge.PredictionLearningProof

open LogicLineages.ComputabilityKnowledge.PredictionGame
open LogicLineages.ComputabilityKnowledge.PredictionLearning
open LogicLineages.ComputabilityKnowledge.Comparators.PredictionLearning

theorem bind_some_iff {α β : Type} (o : Option α) (f : α → Option β) (b : β) :
    o.bind f = some b ↔ ∃ a, o = some a ∧ f a = some b := by
  cases o with
  | none =>
      constructor
      · intro h
        change (none : Option β) = some b at h
        cases h
      · rintro ⟨a, h, _⟩
        cases h
  | some a =>
      constructor
      · intro h
        exact ⟨a, rfl, h⟩
      · rintro ⟨a', h, h'⟩
        cases h
        exact h'

theorem bind_some' {α β : Type} (a : α) (f : α → Option β) : (some a).bind f = f a := rfl

theorem decode_bitValue (b : Bool) : decodeBit (bitValue b) = some b := by
  cases b <;> rfl

theorem boolNe_of_bne {a b : Bool} (h : (a != b) = true) : a ≠ b := by
  intro hab
  subst hab
  cases a <;> exact absurd h (by decide)

theorem bne_of_boolNe {a b : Bool} (h : a ≠ b) : (a != b) = true := by
  cases a <;> cases b
  · exact (h rfl).elim
  · decide
  · decide
  · exact (h rfl).elim

/-! ## Bounded moves agree with the actual policies -/

theorem move_sound (p : Code) (hp : TotalBinary p) (fuel : Nat) (h : List Bool) (b : Bool)
    (hb : boundedMove p fuel h = some b) : policy p hp h = b := by
  obtain ⟨x, hx, hdx⟩ := (bind_some_iff _ _ _).mp hb
  have hxe := Nat.Partrec.Code.evaln_sound (Option.mem_def.mpr hx)
  have hs := Classical.choose_spec (hp h)
  have hxv : x = bitValue (Classical.choose (hp h)) := Part.mem_unique hxe hs
  rw [hxv, decode_bitValue] at hdx
  exact Option.some.inj hdx

theorem move_complete (p : Code) (hp : TotalBinary p) (h : List Bool) :
    ∃ F, ∀ f, F ≤ f → boundedMove p f h = some (policy p hp h) := by
  obtain ⟨F, hF⟩ := Nat.Partrec.Code.evaln_complete.mp (Classical.choose_spec (hp h))
  refine ⟨F, fun f hf => ?_⟩
  have hx := Option.mem_def.mp (Nat.Partrec.Code.evaln_mono hf hF)
  exact (bind_some_iff _ _ _).mpr ⟨_, hx, decode_bitValue _⟩

/-! ## One round of bounded play, in named form -/

def stepFn (a : Code × Code × Nat) (h : List Bool × List Bool) :
    Option (List Bool × List Bool) :=
  (boundedMove a.1 a.2.2 h.1).bind fun x =>
    (boundedMove a.2.1 a.2.2 h.2).bind fun y => some (h.1 ++ [y], h.2 ++ [x])

def errFn (a : Code × Code × Nat) (h : List Bool × List Bool) : Option Bool :=
  (boundedMove a.1 a.2.2 h.1).bind fun x =>
    (boundedMove a.2.1 a.2.2 h.2).bind fun y => some (x != y)

theorem play_succ (p e : Code) (f n : Nat) :
    boundedPlay p e f (n + 1) = (boundedPlay p e f n).bind (stepFn (p, e, f)) := rfl

theorem error_eq (p e : Code) (f n : Nat) :
    boundedError p e f n = (boundedPlay p e f n).bind (errFn (p, e, f)) := rfl

theorem play_step {p e : Code} {f n : Nat} {X Y : List Bool} {a b : Bool}
    (h0 : boundedPlay p e f n = some (X, Y))
    (ha : boundedMove p f X = some a) (hb : boundedMove e f Y = some b) :
    boundedPlay p e f (n + 1) = some (X ++ [b], Y ++ [a]) := by
  rw [play_succ, h0, bind_some']
  show (boundedMove p f X).bind (fun x =>
    (boundedMove e f Y).bind (fun y => some (X ++ [y], Y ++ [x]))) = _
  rw [ha, bind_some', hb, bind_some']

theorem error_step {p e : Code} {f n : Nat} {X Y : List Bool} {a b : Bool}
    (h0 : boundedPlay p e f n = some (X, Y))
    (ha : boundedMove p f X = some a) (hb : boundedMove e f Y = some b) :
    boundedError p e f n = some (a != b) := by
  rw [error_eq, h0, bind_some']
  show (boundedMove p f X).bind (fun x =>
    (boundedMove e f Y).bind (fun y => some (x != y))) = _
  rw [ha, bind_some', hb, bind_some']

/-! ## Bounded plays are actual initial plays, and conversely -/

theorem play_sound (p e : Code) (hp : TotalBinary p) (he : TotalBinary e) (f : Nat) :
    ∀ (n : Nat) (hist : List Bool × List Bool), boundedPlay p e f n = some hist →
      hist = ((histories (policy p hp) (policy e he) n).evasions,
        (histories (policy p hp) (policy e he) n).predictions) := by
  intro n
  induction n with
  | zero =>
      intro hist h
      exact (Option.some.inj h).symm
  | succ n ih =>
      intro hist h
      rw [play_succ] at h
      obtain ⟨h0, hh0, h1⟩ := (bind_some_iff _ _ _).mp h
      have e0 := ih h0 hh0
      subst e0
      obtain ⟨a, ha, h2⟩ := (bind_some_iff _ _ _).mp h1
      obtain ⟨b, hb, h3⟩ := (bind_some_iff _ _ _).mp h2
      have ea := move_sound p hp f _ a ha
      have eb := move_sound e he f _ b hb
      subst ea
      subst eb
      exact (Option.some.inj h3).symm

theorem play_complete (p e : Code) (hp : TotalBinary p) (he : TotalBinary e) (n : Nat) :
    ∃ F, ∀ f, F ≤ f → boundedPlay p e f n =
      some ((histories (policy p hp) (policy e he) n).evasions,
        (histories (policy p hp) (policy e he) n).predictions) := by
  induction n with
  | zero => exact ⟨0, fun f _ => rfl⟩
  | succ n ih =>
      obtain ⟨F0, h0⟩ := ih
      obtain ⟨F1, h1⟩ :=
        move_complete p hp (histories (policy p hp) (policy e he) n).evasions
      obtain ⟨F2, h2⟩ :=
        move_complete e he (histories (policy p hp) (policy e he) n).predictions
      exact ⟨F0 + F1 + F2, fun f hf =>
        play_step (h0 f (by omega)) (h1 f (by omega)) (h2 f (by omega))⟩

/-! ## Error certificates -/

theorem errorSound : ErrorCertificateSound := by
  intro p e hp he fuel n h
  rw [error_eq] at h
  obtain ⟨hist, hh, h1⟩ := (bind_some_iff _ _ _).mp h
  have e0 := play_sound p e hp he fuel n hist hh
  subst e0
  obtain ⟨a, ha, h2⟩ := (bind_some_iff _ _ _).mp h1
  obtain ⟨b, hb, h3⟩ := (bind_some_iff _ _ _).mp h2
  have ea := move_sound p hp fuel _ a ha
  have eb := move_sound e he fuel _ b hb
  subst ea
  subst eb
  exact boolNe_of_bne (Option.some.inj h3)

theorem errorComplete : ErrorCertificateComplete := by
  intro p e hp he n hne
  obtain ⟨F0, h0⟩ := play_complete p e hp he n
  obtain ⟨F1, h1⟩ := move_complete p hp (histories (policy p hp) (policy e he) n).evasions
  obtain ⟨F2, h2⟩ := move_complete e he (histories (policy p hp) (policy e he) n).predictions
  refine ⟨F0 + F1 + F2, ?_⟩
  have hb := error_step (h0 (F0 + F1 + F2) (by omega)) (h1 (F0 + F1 + F2) (by omega))
    (h2 (F0 + F1 + F2) (by omega))
  exact hb.trans (congrArg some (bne_of_boolNe hne))

/-! ## The Sigma-2 learning formula -/

theorem matrix_pair (p e : Code) (c n f : Nat) :
    learningMatrix p e c (Nat.pair n f) =
      if c ≤ n then !((boundedError p e f n).getD false) else true := by
  have h1 : (Nat.pair n f).unpair.1 = n := congrArg Prod.fst (Nat.unpair_pair n f)
  have h2 : (Nat.pair n f).unpair.2 = f := congrArg Prod.snd (Nat.unpair_pair n f)
  unfold learningMatrix
  rw [h1, h2]

theorem learningFormula : LearningFormula := by
  intro p e hp he
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, fun d => ?_⟩
    unfold learningMatrix
    by_cases hcd : c ≤ d.unpair.1
    · rw [if_pos hcd]
      cases hb : boundedError p e d.unpair.2 d.unpair.1 with
      | none => rfl
      | some v =>
          cases v with
          | false => rfl
          | true => exact absurd (hc d.unpair.1 hcd) (errorSound p e hp he _ _ hb)
    · rw [if_neg hcd]
  · rintro ⟨c, hc⟩
    refine ⟨c, fun n hn => ?_⟩
    apply Classical.byContradiction
    intro hne
    obtain ⟨fuel, hf⟩ := errorComplete p e hp he n hne
    have hm := hc (Nat.pair n fuel)
    rw [matrix_pair, if_pos hn, hf] at hm
    exact absurd hm (by decide)

/-! ## Primitive recursiveness of the matrix -/

theorem pr_decodeBit : Primrec decodeBit := by
  have h0 : PrimrecPred (fun n : Nat => n = 0) := Primrec.eq.comp Primrec.id (Primrec.const 0)
  have h1 : PrimrecPred (fun n : Nat => n = 1) := Primrec.eq.comp Primrec.id (Primrec.const 1)
  refine Primrec.of_eq (Primrec.ite h0 (Primrec.const (some false))
    (Primrec.ite h1 (Primrec.const (some true)) (Primrec.const none))) ?_
  intro n
  rfl

theorem pr_move : Primrec (fun x : Code × Nat × List Bool => boundedMove x.1 x.2.1 x.2.2) := by
  have hev : Primrec (fun x : Code × Nat × List Bool =>
      Nat.Partrec.Code.evaln x.2.1 x.1 (Encodable.encode x.2.2)) :=
    Nat.Partrec.Code.primrec_evaln.comp
      (((Primrec.fst.comp Primrec.snd).pair Primrec.fst).pair
        (Primrec.encode.comp (Primrec.snd.comp Primrec.snd)))
  refine Primrec.of_eq (Primrec.option_bind hev (pr_decodeBit.comp Primrec.snd).to₂) ?_
  intro x
  rfl

theorem pr_firstMove : Primrec (fun s : (Code × Code × Nat) × (List Bool × List Bool) =>
    boundedMove s.1.1 s.1.2.2 s.2.1) :=
  pr_move.comp ((Primrec.fst.comp Primrec.fst).pair
    ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.fst.comp Primrec.snd)))

theorem pr_secondMove :
    Primrec (fun t : ((Code × Code × Nat) × (List Bool × List Bool)) × Bool =>
      boundedMove t.1.1.2.1 t.1.1.2.2 t.1.2.2) :=
  pr_move.comp ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
    ((Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
      (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))

theorem pr_step : Primrec₂ stepFn := by
  have hC : Primrec
      (fun u : (((Code × Code × Nat) × (List Bool × List Bool)) × Bool) × Bool =>
        some (u.1.1.2.1 ++ [u.2], u.1.1.2.2 ++ [u.1.2])) :=
    Primrec.option_some.comp
      ((Primrec.list_concat.comp
          (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          Primrec.snd).pair
        (Primrec.list_concat.comp
          (Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
          (Primrec.snd.comp Primrec.fst)))
  refine Primrec.of_eq
    (Primrec.option_bind pr_firstMove (Primrec.option_bind pr_secondMove hC.to₂).to₂) ?_
  intro s
  rfl

theorem pr_errFn : Primrec₂ errFn := by
  have hC : Primrec
      (fun u : (((Code × Code × Nat) × (List Bool × List Bool)) × Bool) × Bool =>
        some (u.1.2 != u.2)) :=
    Primrec.option_some.comp
      ((Primrec.dom_bool₂ (fun x y : Bool => x != y)).comp
        (Primrec.snd.comp Primrec.fst) Primrec.snd)
  refine Primrec.of_eq
    (Primrec.option_bind pr_firstMove (Primrec.option_bind pr_secondMove hC.to₂).to₂) ?_
  intro s
  rfl

theorem pr_play : Primrec₂ (fun (a : Code × Code × Nat) (n : Nat) =>
    boundedPlay a.1 a.2.1 a.2.2 n) := by
  have hg : Primrec₂ (fun (a : Code × Code × Nat)
      (q : Nat × Option (List Bool × List Bool)) => q.2.bind (stepFn a)) :=
    Primrec.option_bind (Primrec.snd.comp Primrec.snd)
      (pr_step.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  refine Primrec₂.of_eq
    (Primrec.nat_rec (Primrec.const (some (([] : List Bool), ([] : List Bool)))) hg) ?_
  intro a n
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun o => Option.bind o (stepFn a)) ih

theorem pr_error : Primrec (fun x : (Code × Code × Nat) × Nat =>
    boundedError x.1.1 x.1.2.1 x.1.2.2 x.2) := by
  have hplay : Primrec (fun x : (Code × Code × Nat) × Nat =>
      boundedPlay x.1.1 x.1.2.1 x.1.2.2 x.2) := pr_play
  refine Primrec.of_eq (Primrec.option_bind hplay
    (pr_errFn.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂) ?_
  intro x
  rfl

theorem pr_matrix : Primrec (fun x : Code × Code × Nat × Nat =>
    learningMatrix x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  have hd : Primrec (fun x : Code × Code × Nat × Nat => x.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hc : Primrec (fun x : Code × Code × Nat × Nat => x.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hu1 : Primrec (fun x : Code × Code × Nat × Nat => x.2.2.2.unpair.1) :=
    Primrec.fst.comp (Primrec.unpair.comp hd)
  have hu2 : Primrec (fun x : Code × Code × Nat × Nat => x.2.2.2.unpair.2) :=
    Primrec.snd.comp (Primrec.unpair.comp hd)
  have herr : Primrec (fun x : Code × Code × Nat × Nat =>
      boundedError x.1 x.2.1 x.2.2.2.unpair.2 x.2.2.2.unpair.1) :=
    pr_error.comp ((Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair hu2)).pair hu1)
  have hget : Primrec (fun x : Code × Code × Nat × Nat =>
      !((boundedError x.1 x.2.1 x.2.2.2.unpair.2 x.2.2.2.unpair.1).getD false)) :=
    Primrec.not.comp (Primrec.option_getD.comp herr (Primrec.const false))
  have hle : PrimrecPred (fun x : Code × Code × Nat × Nat => x.2.2.1 ≤ x.2.2.2.unpair.1) :=
    Primrec.nat_le.comp hc hu1
  refine Primrec.of_eq (Primrec.ite hle hget (Primrec.const true)) ?_
  intro x
  rfl

theorem recursiveMatrix : RecursiveMatrix := pr_matrix.to_comp

theorem sourceLearning :
    LogicLineages.ComputabilityKnowledge.Comparators.PredictionLearning.Target := by
  exact ⟨errorSound, errorComplete, recursiveMatrix, learningFormula⟩

end LogicLineages.ComputabilityKnowledge.PredictionLearningProof
