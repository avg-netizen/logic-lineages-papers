module
public import LogicLineages.OrdinalComparison.ComparisonAssemblyNodeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonAssembly

private theorem fold_prefix {α β : Type} (xs : List α) (default : α) (step : β → α → β) (init : β)
    (n : Nat) (hn : n≤xs.length) :
    Nat.rec init (fun i previous => step previous (xs.getD i default)) n=(xs.take n).foldl step init := by
  induction n with
  | zero => simp
  | succ n ih =>
    change step (Nat.rec init (fun i previous => step previous (xs.getD i default)) n) (xs.getD n default)=_
    rw [ih (by omega),List.take_succ_eq_append_getElem (by omega),List.foldl_append,
      List.foldl_cons,List.foldl_nil,List.getD_eq_getElem xs default (by omega)]

theorem computable_foldl {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → σ} {h : α → σ × β → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldl (fun state item => h a (state,item)) (g a)) := by
  have hitem : Computable (fun p : α × (Nat × σ) => (f p.1).getD p.2.1 default) :=
    (Primrec.list_getD default).to_comp.comp (hf.comp Computable.fst) (Computable.fst.comp Computable.snd)
  have hstep : Computable₂ (fun a : α => fun state : Nat × σ => h a (state.2,(f a).getD state.1 default)) :=
    hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair hitem)
  apply (Computable.nat_rec (Computable.list_length.comp hf) hg hstep).of_eq
  intro a
  rw [fold_prefix (f a) default (fun state item => h a (state,item)) (g a) (f a).length le_rfl]
  simp only [List.take_length]

theorem computable_foldr {α β σ : Type} [Primcodable α] [Primcodable β] [Primcodable σ]
    (default : β) {f : α → List β} {g : α → σ} {h : α → β × σ → σ}
    (hf : Computable f) (hg : Computable g) (hh : Computable₂ h) :
    Computable (fun a => (f a).foldr (fun item state => h a (item,state)) (g a)) := by
  have hs : Computable₂ (fun a : α => fun state : σ × β => h a (state.2,state.1)) :=
    hh.comp Computable.fst ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd))
  apply (computable_foldl default (Computable.list_reverse.comp hf) hg hs).of_eq
  intro a
  rw [List.foldr_eq_foldl_reverse]

end LogicLineages.OrdinalComparison.ComparisonAssembly
