module
public import LogicLineages.StandardControlCurrent.ComputableRecursionTargets

@[expose] public section
namespace LogicLineages.StandardControlCurrent.ComputableFoldProof

variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]

def advance (step : α → σ → β → σ) (a : α) (s : List β × σ) : List β × σ :=
  match s.1 with
  | [] => s
  | b::bs => (bs, step a s.2 b)

theorem advanceProgram {step : α → σ → β → σ}
    (hs : Computable (fun p : α × σ × β => step p.1 p.2.1 p.2.2)) :
    Computable (fun p : α × (List β × σ) => advance step p.1 p.2) := by
  have hh : Computable (fun p : α × (List β × σ) => p.2.1[0]?) :=
    Primrec.list_getElem?.to_comp.comp
      (Computable.fst.comp Computable.snd) (Computable.const 0)
  have hb : Computable₂ (fun p : α × (List β × σ) => fun b : β =>
      (p.2.1.tail, step p.1 p.2.2 b)) := by
    exact ((Primrec.list_tail.to_comp.comp
      (Computable.fst.comp (Computable.snd.comp Computable.fst))).pair
      (hs.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp (Computable.snd.comp Computable.fst)).pair Computable.snd)))).to₂
  apply (Computable.option_casesOn hh Computable.snd hb).of_eq
  rintro ⟨a,xs,s⟩
  cases xs <;> rfl

theorem advanceIterate (step : α → σ → β → σ) (a : α) (xs : List β) (s : σ) :
    (advance step a)^[xs.length] (xs,s) = ([],xs.foldl (step a) s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simpa only [List.length_cons, Function.iterate_succ_apply, advance, List.foldl_cons]
      using ih (step a s b)

theorem listFold : ComputableRecursionTargets.ListFold := by
  intro α β σ _ _ _ xs initial step hx hi hs
  have had := advanceProgram hs
  have hrun : Computable (fun a =>
      Nat.rec (motive := fun _ => List β × σ) (xs a, initial a)
        (fun _ s => advance step a s) (xs a).length) :=
    Computable.nat_rec (Primrec.list_length.to_comp.comp hx) (hx.pair hi)
      (had.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))).to₂
  have hEq (a : α) :
      Nat.rec (motive := fun _ => List β × σ) (xs a, initial a)
        (fun _ s => advance step a s) (xs a).length =
      ([], (xs a).foldl (step a) (initial a)) := by
    rw [show (Nat.rec (motive := fun _ => List β × σ) (xs a, initial a)
        (fun _ s => advance step a s) (xs a).length) =
        (advance step a)^[(xs a).length] (xs a,initial a) by
      generalize (xs a).length = n
      induction n with
      | zero => rfl
      | succ n ih => simpa only [Nat.rec_add_one, Function.iterate_succ_apply'] using congrArg (advance step a) ih]
    exact advanceIterate step a (xs a) (initial a)
  exact (Computable.snd.comp hrun).of_eq (fun a => congrArg Prod.snd (hEq a))


theorem filterMapProgram {xs : α → List β} {g : α → β → Option σ}
    (hx : Computable xs) (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (xs a).filterMap (g a)) := by
  have hs : Computable (fun p : α × List σ × β =>
      p.2.1 ++ (g p.1 p.2.2).toList) :=
    Primrec.list_append.to_comp.comp (Computable.fst.comp Computable.snd)
      (Primrec.optionToList.to_comp.comp
        (hg.comp (Computable.fst.pair (Computable.snd.comp Computable.snd))))
  have h := listFold α β (List σ) xs (fun _ => [])
    (fun a acc b => acc ++ (g a b).toList) hx (Computable.const []) hs
  apply h.of_eq
  intro a
  have he (bs : List β) (acc : List σ) :
      bs.foldl (fun acc b => acc ++ (g a b).toList) acc = acc ++ bs.filterMap (g a) := by
    induction bs generalizing acc with
    | nil => simp
    | cons b bs ih =>
      simp only [List.foldl_cons, ih, List.filterMap_cons]
      cases g a b <;> simp [List.append_assoc]
  simpa using he (xs a) []

end LogicLineages.StandardControlCurrent.ComputableFoldProof
