module
public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE

@[expose] public section
namespace LogicLineages.PermittedControl.UniformPolicyCompiler

/-! Generic tools: recursion through Kleene's fixed-point theorem, and binding
inside `Part (Option _)` with the inner `none` kept as rejection. -/

section Fix
variable {α σ : Type} [Primcodable α] [Primcodable σ]

/-- Decoded evaluation of an ordinary program at an encoded argument. -/
def decodeEval (c : Nat.Partrec.Code) (a : α) : Part σ :=
  (c.eval (Encodable.encode a)).bind (fun m => ((Encodable.decode m : Option σ) : Part σ))

theorem decodeEvalPartrec :
    Partrec (fun x : Nat.Partrec.Code × α => (decodeEval x.1 x.2 : Part σ)) := by
  have he : Partrec (fun x : Nat.Partrec.Code × α => x.1.eval (Encodable.encode x.2)) :=
    Nat.Partrec.Code.eval_part.comp Computable.fst (Computable.encode.comp Computable.snd)
  have hd : Partrec₂ (fun (_ : Nat.Partrec.Code × α) (m : Nat) => ((Encodable.decode m : Option σ) : Part σ)) :=
    (Computable.ofOption (Computable.decode.comp Computable.snd)).to₂
  exact he.bind hd

/-- One recursion through the fixed-point theorem: a one-step functional whose
instance at decoded program evaluation is partial recursive in the program
and the argument has a partial recursive fixed point. -/
theorem exists_fix (Φ : (α →. σ) → α →. σ)
    (hΦ : Partrec (fun x : Nat.Partrec.Code × α => Φ (decodeEval x.1) x.2)) :
    ∃ G : α →. σ, Partrec G ∧ ∀ a, G a = Φ G a := by
  let f : Nat.Partrec.Code → Nat →. Nat := fun c n =>
    ((Encodable.decode n : Option α) : Part α).bind (fun a => (Φ (decodeEval c) a).map Encodable.encode)
  have hf : Partrec₂ f := by
    have hdec : Partrec (fun x : Nat.Partrec.Code × Nat => ((Encodable.decode x.2 : Option α) : Part α)) :=
      Computable.ofOption (Computable.decode.comp Computable.snd)
    have hstep : Partrec₂ (fun (x : Nat.Partrec.Code × Nat) (a : α) =>
        (Φ (decodeEval x.1) a).map Encodable.encode) := by
      have h1 : Partrec (fun y : (Nat.Partrec.Code × Nat) × α => Φ (decodeEval y.1.1) y.2) :=
        hΦ.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)
      exact (h1.map (Computable.encode.comp Computable.snd).to₂).to₂
    exact (hdec.bind hstep).to₂
  obtain ⟨c0,hc0⟩ := Nat.Partrec.Code.fixed_point₂ hf
  refine ⟨decodeEval c0,?_,?_⟩
  · exact decodeEvalPartrec.comp ((Computable.const c0).pair Computable.id)
  · intro a
    have h : (decodeEval c0 a : Part σ) =
        (Nat.Partrec.Code.eval c0 (Encodable.encode a)).bind
          (fun m => ((Encodable.decode m : Option σ) : Part σ)) := rfl
    rw [h,hc0]
    simp only [f,Encodable.encodek,Part.coe_some,Part.bind_some,Part.bind_map,Part.bind_some_right]

end Fix

section Bind

/-- Bind inside `Part (Option _)`: divergence propagates, inner `none` is kept. -/
def pbind {β γ : Type} (x : Part (Option β)) (f : β → Part (Option γ)) : Part (Option γ) :=
  x.bind (fun o => Option.casesOn o (Part.some none) f)

theorem pbindPartrec {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    {x : α →. Option β} {f : α → β →. Option γ} (hx : Partrec x) (hf : Partrec₂ f) :
    Partrec (fun a => pbind (x a) (f a)) := by
  have hcase : Partrec₂ (fun (a : α) (o : Option β) => Option.casesOn o (Part.some none) (f a)) := by
    have h := Partrec.optionCasesOn_right (o := fun y : α × Option β => y.2)
      (f := fun _ => (none : Option γ)) (g := fun y : α × Option β => f y.1)
      Computable.snd (Computable.const none) (hf.comp (Computable.fst.comp Computable.fst) Computable.snd)
    exact h.to₂
  exact hx.bind hcase

@[simp] theorem pbind_some_some {β γ : Type} (b : β) (f : β → Part (Option γ)) :
    pbind (Part.some (some b)) f = f b := by
  simp [pbind]

@[simp] theorem pbind_some_none {β γ : Type} (f : β → Part (Option γ)) :
    pbind (Part.some (none : Option β)) f = Part.some none := by
  simp [pbind]

/-- Calibration of a bind whose continuation is calibrated. -/
theorem pbind_calibrated {β γ : Type} (o : Option β) (f : β → Part (Option γ)) (g : β → Option γ)
    (h : ∀ b, f b = Part.some (g b)) : pbind (Part.some o) f = Part.some (o.bind g) := by
  cases o with
  | none => simp
  | some b => simp [h b]

/-- Partial if-then-else on a decidable proposition with a computable test. -/
theorem pite {α σ : Type} [Primcodable α] [Primcodable σ] {P : α → Prop} [DecidablePred P]
    {f g : α →. σ} (hP : Computable (fun a => decide (P a))) (hf : Partrec f) (hg : Partrec g) :
    Partrec (fun a => if P a then f a else g a) := by
  have h := Partrec.cond hP hf hg
  refine h.of_eq (fun a => ?_)
  by_cases hp : P a <;> simp [hp]

end Bind

end LogicLineages.PermittedControl.UniformPolicyCompiler
