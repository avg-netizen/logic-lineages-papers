module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem nodePrim {α : Type*} [Primcodable α] {t a b : α → Nat}
    (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node (t x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp ha hb)) ht

private theorem freePrim {α : Type*} [Primcodable α] {l i n : α → Nat}
    (hl : Primrec l) (hi : Primrec i) (hn : Primrec n) :
    Primrec (fun x => partialFree (l x) (i x) (n x)) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hl (Primrec.const 2)))
  exact Primrec.ite (Primrec.eq.comp (hi.comp Primrec.fst) Primrec.snd)
    (nodePrim (Primrec.const 4)
      (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp (hn.comp Primrec.fst))
      (Primrec.const 1)) (Primrec.const 1)

private theorem mergePrim {α : Type*} [Primcodable α] {l t : α → Nat} {a b : α → List Nat}
    (hl : Primrec l) (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => partialMerge (l x) (t x) (a x) (b x)) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hl (Primrec.const 2)))
  have hga := (Primrec.list_getD 0).comp (ha.comp Primrec.fst) Primrec.snd
  have hgb := (Primrec.list_getD 0).comp (hb.comp Primrec.fst) Primrec.snd
  exact nodePrim (Primrec.const 4)
    (nodePrim (Primrec.const 4)
      (Primrec.ite (Primrec.eq.comp (ht.comp Primrec.fst) (Primrec.const 5))
        (nodePrim (Primrec.const 4) hga hga) hga) hgb) (Primrec.const 1)

private theorem collapsePrim {α : Type*} [Primcodable α] {l h : α → Nat} {a b : α → List Nat}
    (hl : Primrec l) (hh : Primrec h) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => partialCollapse (l x) (h x) (a x) (b x)) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hl (Primrec.const 2)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (nodePrim (Primrec.const 6)
      (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp (hh.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (hb.comp Primrec.fst) (Primrec.const 0)))
    (nodePrim (Primrec.const 4)
      ((Primrec.list_getD 0).comp (ha.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (hb.comp Primrec.fst) Primrec.snd))

private theorem bindTwoPrim {α : Type*} [Primcodable α]
    {a b : α → Option (List Nat)} {f : α → List Nat → List Nat → List Nat}
    (ha : Primrec a) (hb : Primrec b)
    (hf : Primrec (fun p : α × List Nat × List Nat => f p.1 p.2.1 p.2.2)) :
    Primrec (fun x => do let u ← a x; let v ← b x; pure (f x u v)) := by
  have hmap := Primrec.option_map (hb.comp Primrec.fst)
    (hf.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))).to₂
  have hbind := Primrec.option_bind ha hmap.to₂
  apply hbind.of_eq
  intro x
  change (a x).bind (fun u => (b x).map (f x u)) = _
  cases ha' : a x <;> cases hb' : b x <;> simp [ha', hb']

theorem ordinalSyntaxPartialPrimitiveRecursive : Targets.OrdinalSyntaxPartialPrimitiveRecursive := by
  let branch : Nat → Prop := fun n => n%8=4 ∨ n%8=5 ∨ n%8=6
  let children : (Nat × Nat × Nat) → List (Nat × Nat × Nat) := fun p =>
    if branch p.2.2 then
      [(p.1, (if p.2.2%8=4 then p.2.1 else if p.2.2%8=5 then p.2.1+1 else 1), (p.2.2/8).unpair.1),
       (p.1, (if p.2.2%8=6 then 0 else p.2.1), (p.2.2/8).unpair.2)]
    else []
  let assemble : (Nat × Nat × Nat) → List (Option (List Nat)) → Option (Option (List Nat)) :=
    fun p rs => some (
      if headFree p.2.2 then some (partialFree p.1 p.2.1 p.2.2)
      else if p.2.2%8=3 then
        if p.2.1=(p.2.2/8).unpair.2 then some (List.replicate (p.1+2) 1) else none
      else if branch p.2.2 then
        if p.2.2%8=4 then do
          let a ← rs.getD 0 none; let b ← rs.getD 1 none
          pure (partialMerge p.1 4 a b)
        else if p.2.2%8=5 then
          if 0<p.2.1 then do
            let a ← rs.getD 0 none; let b ← rs.getD 1 none
            pure (partialMerge p.1 5 a b)
          else none
        else if p.2.1=0 then do
          let a ← rs.getD 0 none; let b ← rs.getD 1 none
          pure (partialCollapse p.1 (p.2.2/8).unpair.1 a b)
        else none
      else none)
  have hlevel : Primrec (fun p : Nat × Nat × Nat => p.1) := Primrec.fst
  have hi : Primrec (fun p : Nat × Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : Nat × Nat × Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have ht := Primrec.nat_mod.comp hn (Primrec.const 8)
  have hd := Primrec.unpair.comp (Primrec.nat_div.comp hn (Primrec.const 8))
  have he (k : Nat) : PrimrecPred (fun p : Nat × Nat × Nat => p.2.2%8=k) :=
    Primrec.eq.comp ht (Primrec.const k)
  have hbranch : PrimrecPred (fun p : Nat × Nat × Nat => branch p.2.2) :=
    (he 4).or ((he 5).or (he 6))
  have hchildren : Primrec children :=
    Primrec.ite hbranch
      (Primrec.list_cons.comp
        (hlevel.pair ((Primrec.ite (he 4) hi (Primrec.ite (he 5)
          (Primrec.succ.comp hi) (Primrec.const 1))).pair (Primrec.fst.comp hd)))
        (Primrec.list_cons.comp
          (hlevel.pair ((Primrec.ite (he 6) (Primrec.const 0) hi).pair (Primrec.snd.comp hd)))
          (Primrec.const []))) (Primrec.const [])
  have hrep : Primrec (fun p : Nat × Nat × Nat => List.replicate (p.1+2) 1) := by
    have h := Primrec.list_map (Primrec.list_range.comp
      (Primrec.nat_add.comp hlevel (Primrec.const 2))) (Primrec.const 1).to₂
    exact h.of_eq (fun p => by simp)
  have ha : Primrec₂ assemble := by
    have hget (k : Nat) : Primrec (fun p : (Nat × Nat × Nat) × List (Option (List Nat)) =>
        p.2.getD k none) := (Primrec.list_getD none).comp Primrec.snd (Primrec.const k)
    have hm (k : Nat) : Primrec (fun x : (Nat × Nat × Nat) × List (Option (List Nat)) => do
        let a ← x.2.getD 0 none
        let b ← x.2.getD 1 none
        pure (partialMerge x.1.1 k a b)) := by
      have h := mergePrim
        (α := (((Nat × Nat × Nat) × List (Option (List Nat))) × List Nat × List Nat))
        (l := fun p => p.1.1.1) (t := fun _ => k)
        (a := fun p => p.2.1) (b := fun p => p.2.2)
        (hlevel.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const k)
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      have hh := bindTwoPrim (α := (Nat × Nat × Nat) × List (Option (List Nat)))
        (f := fun x a b => partialMerge x.1.1 k a b) (hget 0) (hget 1) h
      exact hh.of_eq (fun x => rfl)
    have hc : Primrec (fun x : (Nat × Nat × Nat) × List (Option (List Nat)) => do
        let a ← x.2.getD 0 none
        let b ← x.2.getD 1 none
        pure (partialCollapse x.1.1 (x.1.2.2/8).unpair.1 a b)) := by
      have h := collapsePrim
        (α := (((Nat × Nat × Nat) × List (Option (List Nat))) × List Nat × List Nat))
        (l := fun p => p.1.1.1) (h := fun p => (p.1.1.2.2/8).unpair.1)
        (a := fun p => p.2.1) (b := fun p => p.2.2)
        (hlevel.comp (Primrec.fst.comp Primrec.fst))
        ((Primrec.fst.comp hd).comp (Primrec.fst.comp Primrec.fst))
        (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
      have hh := bindTwoPrim (α := (Nat × Nat × Nat) × List (Option (List Nat)))
        (f := fun x a b => partialCollapse x.1.1 (x.1.2.2/8).unpair.1 a b) (hget 0) (hget 1) h
      exact hh.of_eq (fun x => rfl)
    exact Primrec.option_some.comp (Primrec.ite
      (Primrec.eq.comp (ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp (hn.comp Primrec.fst))
        (Primrec.const true))
      (Primrec.option_some.comp (freePrim (hlevel.comp Primrec.fst)
        (hi.comp Primrec.fst) (hn.comp Primrec.fst)))
      (Primrec.ite ((he 3).comp Primrec.fst)
        (Primrec.ite ((Primrec.eq.comp hi (Primrec.snd.comp hd)).comp Primrec.fst)
          (Primrec.option_some.comp (hrep.comp Primrec.fst)) (Primrec.const none))
        (Primrec.ite (hbranch.comp Primrec.fst)
          (Primrec.ite ((he 4).comp Primrec.fst) (hm 4)
            (Primrec.ite ((he 5).comp Primrec.fst)
              (Primrec.ite ((Primrec.nat_lt.comp (Primrec.const 0) hi).comp Primrec.fst)
                (hm 5) (Primrec.const none))
              (Primrec.ite ((Primrec.eq.comp hi (Primrec.const 0)).comp Primrec.fst)
                hc (Primrec.const none)))) (Primrec.const none))))
  apply Primrec.nat_omega_rec' (fun p : Nat × Nat × Nat => partialRun p.1 p.2.1 p.2.2)
    hn hchildren ha
  · intro p c hc
    by_cases h : branch p.2.2
    · have hpos : 0<p.2.2 := by dsimp [branch] at h; omega
      have hdiv := Nat.div_lt_self hpos (show 1<8 by decide)
      simp only [children, if_pos h, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact (Nat.unpair_left_le _).trans_lt hdiv
      · exact (Nat.unpair_right_le _).trans_lt hdiv
    · simp [children, h] at hc
  · rintro ⟨level, i, n⟩
    conv_rhs => rw [partialRun]
    by_cases hf : headFree n = true
    · simp [assemble, hf]
    · by_cases h3 : n%8=3
      · simp [assemble, hf, h3]
      · by_cases h4 : n%8=4
        · have h5 : n%8≠5 := by omega
          have h6 : n%8≠6 := by omega
          simp [assemble, children, branch, hf, h3, h4, h5, h6]
        · by_cases h5 : n%8=5
          · have h6 : n%8≠6 := by omega
            by_cases hi : (0 < i) <;>
              simp [assemble, children, branch, hf, h3, h4, h5, h6, hi]
          · by_cases h6 : n%8=6
            · by_cases hi : (i = 0) <;>
                simp [assemble, children, branch, hf, h3, h4, h5, h6, hi]
            · simp [assemble, children, branch, hf, h3, h4, h5, h6]
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
