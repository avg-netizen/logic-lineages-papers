module
public import LogicLineages.OrdinalComparison.OrdinalSyntaxComputableFoldTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntaxComputableFold.Proof

/-- The actual raw fold recurses on strictly smaller decoded child codes. -/
theorem exactRawRecursion : Targets.ExactRawRecursion := by
  constructor
  · intro n hn
    have hnpos : 0 < n := by unfold atom at hn; omega
    have hd : n/8 < n := Nat.div_lt_self hnpos (by decide)
    exact ⟨(Nat.unpair_left_le _).trans_lt hd,(Nat.unpair_right_le _).trans_lt hd⟩
  · intro P A leaf branch p n
    change OrdinalSyntax.fold (fun k => leaf (p,k))
      (fun k a b => branch (p,k,a,b)) n = _
    rw [OrdinalSyntax.fold] <;> rfl

attribute [local irreducible] Nat.unpair Nat.sqrt Computable Partrec indexedFold

/-- A first-order table assembly step, with a supplied leaf value as fallback. -/
private def assemble {P A : Type} (leaf : P × Nat → A)
    (branch : P × (Nat × A × A) → A) (p : P) (xs : List A) : Option A :=
  some (if atom xs.length then leaf (p,xs.length) else
    branch (p,xs.length%8,
      (xs[(xs.length/8).unpair.1]?).getD (leaf (p,0)),
      (xs[(xs.length/8).unpair.2]?).getD (leaf (p,0))))

private theorem assemble_computable {P A : Type} [Primcodable P] [Primcodable A]
    (leaf : P × Nat → A) (branch : P × (Nat × A × A) → A)
    (hl : Computable leaf) (hb : Computable branch) : Computable₂ (assemble leaf branch) := by
  have hn : Primrec (fun x : P × List A => x.2.length) :=
    Primrec.list_length.comp Primrec.snd
  have ht := Primrec.nat_mod.comp hn (Primrec.const 8)
  have hp := Primrec.unpair.comp (Primrec.nat_div.comp hn (Primrec.const 8))
  have ha : PrimrecPred (fun x : P × List A => atom x.2.length) :=
    (Primrec.nat_lt.comp ht (Primrec.const 4)).or (Primrec.eq.comp ht (Primrec.const 7))
  have hdefault : Computable (fun x : P × List A => leaf (x.1,0)) :=
    hl.comp (Computable.fst.pair (Computable.const 0))
  have hleft : Computable (fun x : P × List A =>
      (x.2[(x.2.length/8).unpair.1]?).getD (leaf (x.1,0))) :=
    Computable.option_getD
      (Computable.list_getElem?.comp Computable.snd (Primrec.fst.comp hp).to_comp) hdefault
  have hright : Computable (fun x : P × List A =>
      (x.2[(x.2.length/8).unpair.2]?).getD (leaf (x.1,0))) :=
    Computable.option_getD
      (Computable.list_getElem?.comp Computable.snd (Primrec.snd.comp hp).to_comp) hdefault
  have hleaf : Computable (fun x : P × List A => leaf (x.1,x.2.length)) :=
    hl.comp (Computable.fst.pair hn.to_comp)
  have hbranch : Computable (fun x : P × List A =>
      branch (x.1,x.2.length%8,
        (x.2[(x.2.length/8).unpair.1]?).getD (leaf (x.1,0)),
        (x.2[(x.2.length/8).unpair.2]?).getD (leaf (x.1,0)))) :=
    hb.comp (Computable.fst.pair (ht.to_comp.pair (hleft.pair hright)))
  have hite : Computable (fun x : P × List A =>
      if atom x.2.length then leaf (x.1,x.2.length) else
        branch (x.1,x.2.length%8,
          (x.2[(x.2.length/8).unpair.1]?).getD (leaf (x.1,0)),
          (x.2[(x.2.length/8).unpair.2]?).getD (leaf (x.1,0)))) := by
    simpa only [Bool.cond_decide] using Computable.cond ha.decide.to_comp hleaf hbranch
  exact (Computable.option_some.comp hite).to₂

private theorem assemble_correct {P A : Type} (leaf : P × Nat → A)
    (branch : P × (Nat × A × A) → A) (p : P) (n : Nat) :
    assemble leaf branch p ((List.range n).map (indexedFold leaf branch p)) =
      some (indexedFold leaf branch p n) := by
  unfold assemble
  simp only [List.length_map,List.length_range]
  rw [exactRawRecursion.2 P A leaf branch p n]
  by_cases h : atom n
  · simp only [if_pos h]
  · obtain ⟨hleft,hright⟩ := exactRawRecursion.1 n h
    simp only [if_neg h,List.getElem?_map,List.getElem?_range hleft,
      List.getElem?_range hright,Option.map_some,Option.getD_some]

/-- Computable leaf and branch operations induce a computable indexed raw fold. -/
theorem indexedComputable : Targets.IndexedComputable := by
  intro P A _ _ leaf branch hl hb
  exact Computable.nat_strong_rec (indexedFold leaf branch)
    (assemble_computable leaf branch hl hb) (assemble_correct leaf branch)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntaxComputableFold.Proof
