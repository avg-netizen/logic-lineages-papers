module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeTargets
public import LogicLineages.OrdinalComparison.ComparisonAssemblyListProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
open PlainBlockDispatchCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem ite_program {α β : Type} [Primcodable α] [Primcodable β]
    {c : α → Prop} [DecidablePred c] {f g : α → β}
    (hc : PrimrecPred c) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if c a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hc.decide.to_comp hf hg
#print axioms ite_program

theorem map_program {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    (default : β) {xs : α → List β} {f : α → β → γ}
    (hx : Computable xs) (hf : Computable₂ f) :
    Computable (fun a => (xs a).map (f a)) := by
  have hs : Computable₂ (fun a : α => fun s : β × List γ => f a s.1 :: s.2) :=
    Computable.list_cons.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr_cons, List.map_cons, ih]
#print axioms map_program

theorem flatMap_program {α β γ : Type} [Primcodable α] [Primcodable β] [Primcodable γ]
    (default : β) {xs : α → List β} {f : α → β → List γ}
    (hx : Computable xs) (hf : Computable₂ f) :
    Computable (fun a => (xs a).flatMap (f a)) := by
  have hs : Computable₂ (fun a : α => fun s : β × List γ => f a s.1 ++ s.2) :=
    Computable.list_append.comp (hf.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr default hx (Computable.const []) hs).of_eq
  intro a
  induction xs a with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr_cons, List.flatMap_cons, ih]
#print axioms flatMap_program

theorem erase_primitive : Primrec₂ (fun (xs : List Nat) (i : Nat) => xs.erase i) := by
  have hs : Primrec₂ (fun p : List Nat × Nat => fun s : Nat × (List Nat × List Nat) =>
      if s.1 == p.2 then s.2.1 else s.1 :: s.2.2) :=
    Primrec.ite (Primrec.eq.comp
      (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.const true))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  apply (Primrec.list_rec Primrec.fst (Primrec.const []) hs).of_eq
  intro p
  induction p.1 with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.erase_cons] using
        congrArg (fun ys : List Nat => if x == p.2 then xs else x :: ys) ih
#print axioms erase_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
