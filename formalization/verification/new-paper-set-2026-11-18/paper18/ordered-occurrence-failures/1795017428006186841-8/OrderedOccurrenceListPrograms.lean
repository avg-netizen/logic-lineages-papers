module
public import LogicLineages.StandardControlCurrent.ComputableFoldProof
public import LogicLineages.OrdinalComparison.ComparisonAssemblyListProof
public import Mathlib.Data.List.Enum
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceListPrograms
open OrdinalComparison
variable {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]

theorem mapC (default : β) {f : α → List β} {g : α → β → σ}
    (hf : Computable f) (hg : Computable₂ g) : Computable (fun a => (f a).map (g a)) := by
  have step : Computable₂ (fun a : α => fun q : β × List σ => g a q.1 :: q.2) :=
    Primrec.list_cons.to_comp.comp (hg.comp Computable.fst (Computable.fst.comp Computable.snd))
      (Computable.snd.comp Computable.snd)
  apply (ComparisonAssembly.computable_foldr default hf (Computable.const []) step).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b bs ih => simp only [List.foldr_cons,List.map_cons,ih]

theorem flatMapC (default : β) {f : α → List β} {g : α → β → List σ}
    (hf : Computable f) (hg : Computable₂ g) : Computable (fun a => (f a).flatMap (g a)) :=
  Primrec.list_flatten.to_comp.comp (mapC default hf hg)

theorem zipIdxP : Primrec (fun xs : List α => xs.zipIdx) := by
  have step : Primrec₂ (fun (_ : List α) => fun s : α × List α × List (α × Nat) =>
      (s.1,0) :: s.2.2.map (fun q => (q.1,q.2+1))) := by
    have hmap := Primrec.list_map (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.nat_add.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 1))).to₂
    exact Primrec.list_cons.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.const 0)) hmap
  apply (Primrec.list_rec Primrec.id (Primrec.const []) step).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.zipIdx_cons',id_eq,List.rec_cons,Prod.map] using congrArg (fun z : List (α × Nat) => (x,0)::z.map (fun q => (q.1,q.2+1))) ih

theorem eraseP : Primrec (fun q : List Nat × Nat => q.1.erase q.2) := by
  have hs : Primrec₂ (fun q : List Nat × Nat => fun step : Nat × List Nat × List Nat =>
      if step.1=q.2 then step.2.1 else step.1::step.2.2) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.fst))
      (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  apply (Primrec.list_rec Primrec.fst (Primrec.const []) hs).of_eq
  intro q
  induction q.1 with
  | nil => rfl
  | cons x xs ih => simp only [List.erase_cons,beq_iff_eq,ih]

theorem memberP : Primrec (fun q : Nat × List Nat => decide (q.1∈q.2)) := by
  have h := (Primrec.eq : PrimrecRel (fun a b : Nat => a=b)).exists_mem_list
  exact (h.comp Primrec.snd Primrec.fst).decide.of_eq (by intro q; simp)
theorem filterP {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).filter (g a)) := by
  have step : Primrec₂ (fun a : α => fun q : β × List β => if g a q.1 then q.1::q.2 else q.2) :=
    Primrec.ite (Primrec.eq.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.const true))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hf (Primrec.const []) step).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b bs ih => simp only [List.filter_cons,List.foldr_cons,ih]

theorem anyP {f : α → List β} {g : α → β → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) := by
  have step : Primrec₂ (fun a : α => fun q : β × Bool => g a q.1 || q.2) :=
    Primrec.or.comp (hg.comp Primrec.fst (Primrec.fst.comp Primrec.snd)) (Primrec.snd.comp Primrec.snd)
  apply (Primrec.list_foldr hf (Primrec.const false) step).of_eq
  intro a
  induction f a with
  | nil => rfl
  | cons b bs ih => simp only [List.any_cons,List.foldr_cons,ih]

end LogicLineages.StandardControlCurrent.OrderedOccurrenceListPrograms
