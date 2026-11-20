module

public import LogicLineages.PersistentMarking.NumberedWindowClassProgramTargets
import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowClassProgramProof
open NumberedWindowClassAlgorithm NumberedWindowClassProgramTargets LogicLineages.ComputabilityKnowledge List.Vector

private theorem filterWith {α γ} [Primcodable α] [Primcodable γ]
    {f : α → γ → Bool} (hf : Primrec₂ f) :
    Primrec₂ (fun (xs : List α) (c : γ) => xs.filter (fun a => f a c)) := by
  have h : PrimrecRel (fun a c => f a c = true) := Primrec.eq.comp hf (Primrec.const true)
  exact h.listFilter.of_eq (by simp)

private theorem anyWith {α γ} [Primcodable α] [Primcodable γ]
    {f : α → γ → Bool} (hf : Primrec₂ f) :
    Primrec₂ (fun (xs : List α) (c : γ) => xs.any (fun a => f a c)) := by
  have h : PrimrecRel (fun a c => f a c = true) := Primrec.eq.comp hf (Primrec.const true)
  apply h.exists_mem_list.decide.to₂.of_eq
  intro xs c
  apply Bool.eq_iff_iff.mpr
  simp

private theorem minimum : Primrec (List.min? (α := Nat)) := by
  have folder := Primrec.list_foldl Primrec.list_tail (Primrec.list_headI : Primrec (@List.headI Nat _))
    (Primrec.nat_min.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
  apply (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const ([] : List Nat)))
    (Primrec.const none) (Primrec.option_some.comp folder)).of_eq
  intro xs
  cases xs <;> rfl

abbrev Input := Nat × Nat × Nat

private theorem memberValues (cover : Nat → List Nat) (edge : Nat → Nat → Nat → Nat → Bool)
    (hc : Primrec cover) (he : Primrec (fun p : ExchangeInput => edge p.1 p.2.1 p.2.2.1 p.2.2.2)) :
    Primrec (fun p : Input => members (edge p.1 p.2.1) (cover p.2.2) p.2.2) := by
  have seed : Primrec (fun p : Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have vs := hc.comp seed
  have equalNat : Primrec₂ (fun (a b : Nat) => b == a) :=
    ((Primrec.eq.comp Primrec.snd Primrec.fst).decide).of_eq (fun _ => by apply Bool.eq_iff_iff.mpr; simp)
  have base := (filterWith equalNat).comp vs seed
  let rel := fun (w : Nat) (p : Nat × Input) => w == p.1 || edge p.2.1 p.2.2.1 w p.1
  have w : Primrec (fun p : Nat × Nat × Input => p.1) := Primrec.fst
  have v : Primrec (fun p : Nat × Nat × Input => p.2.1) := Primrec.fst.comp Primrec.snd
  have input : Primrec (fun p : Nat × Nat × Input => p.2.2) := Primrec.snd.comp Primrec.snd
  have relPr : Primrec₂ rel := Primrec.or.comp (equalNat.comp v w)
    (he.comp ((Primrec.fst.comp input).pair ((Primrec.fst.comp (Primrec.snd.comp input)).pair (w.pair v))))
  have test : Primrec₂ (fun (v : Nat) (p : Input × List Nat) => p.2.any (fun w => rel w (v,p.1))) :=
    (anyWith relPr).comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))
  have update := (filterWith test).comp (vs.comp Primrec.fst) Primrec.id
  have step : Primrec₂ (fun (p : Input) (st : Nat × List Nat) => advance (edge p.1 p.2.1) (cover p.2.2) st.2) :=
    update.comp (Primrec.fst.pair (Primrec.snd.comp Primrec.snd))
  have recurrence := Primrec.nat_rec base step
  have each : Primrec₂ (fun (p : Input) n => rounds (edge p.1 p.2.1) (cover p.2.2) p.2.2 n) := by
    apply recurrence.of_eq
    intro p n
    induction n with
    | zero => rfl
    | succ n ih =>
      change advance _ _ _ = advance _ _ _
      rw [ih]
  exact each.comp Primrec.id (Primrec.list_length.comp vs)

private theorem three {α} [Primcodable α] (f : Input → α) (hf : Primrec f) :
    ∃ p : GorbowPRProgram.Program 3, ∀ a b c,
      GorbowPRProgram.evaluate p (a ::ᵥ b ::ᵥ c ::ᵥ List.Vector.nil) = Encodable.encode (f (a,b,c)) := by
  have first : Primrec (fun v : List.Vector Nat 3 => v.head) := Primrec.vector_head
  have second := Primrec.vector_head.comp (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail))
  have third := Primrec.vector_head.comp (Primrec.vector_tail.comp
    (Primrec.vector_tail : Primrec (fun v : List.Vector Nat 3 => v.tail)))
  obtain ⟨p,eval⟩ := GorbowPRProgram.Proof.allPrimitiveFunctions 3 _
    (Primrec.encode.comp (hf.comp (first.pair (second.pair third))))
  exact ⟨p,fun a b c => eval (a ::ᵥ b ::ᵥ c ::ᵥ List.Vector.nil)⟩

theorem programs : ClassPrograms := by
  intro cover edge hc he
  have h := memberValues cover edge hc he
  exact ⟨three _ h,three _ (minimum.comp h)⟩

end LogicLineages.PersistentMarking.NumberedWindowClassProgramProof
