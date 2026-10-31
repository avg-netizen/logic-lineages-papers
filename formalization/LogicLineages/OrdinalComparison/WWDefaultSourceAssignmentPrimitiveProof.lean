module
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxStatementChecks
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxAbstractionStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.Proof
open SyntaxCode OrdinalSyntax

theorem primeCodePrimitiveRecursive : Primrec (fun p : Nat×Nat×Nat => primeCode p.1 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : Nat×Nat×Nat => (List.range (p.2.2+1)).map (fun i =>
      if p.1=0 then 8*Nat.pair p.2.1 i+3 else if p.1=4 then
        if i=0 then repeatCode 2 1 else if i=typeLevel p.2.1+2 then 2 else 1
      else 1)) := by
    apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.snd.comp Primrec.snd)))
    have ht := Primrec.fst.comp Primrec.fst (α := (Nat×Nat×Nat)×Nat)
    have hpay : Primrec (fun p : (Nat×Nat×Nat)×Nat => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp hpay Primrec.snd)) (Primrec.const 3))
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4))
        (Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const (repeatCode 2 1))
          (Primrec.ite (Primrec.eq.comp Primrec.snd
            (Primrec.nat_add.comp (SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive.comp hpay) (Primrec.const 2)))
            (Primrec.const 2) (Primrec.const 1))) (Primrec.const 1))
  exact hp.of_eq (fun p => by
    by_cases h0 : p.1=0 <;> by_cases h4 : p.1=4 <;> simp [primeCode,h0,h4])

private theorem appBindPrimitive : Primrec (fun p : Nat×Nat×Option (List Nat)×Option (List Nat) =>
    p.2.2.1.bind (fun f => p.2.2.2.map (fun a => defaultApplicationCode p.1 p.2.1 f a))) := by
  apply Primrec.option_bind (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  apply Primrec.option_map (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  let P := ((Nat×Nat×Option (List Nat)×Option (List Nat))×List Nat)×List Nat
  have h1 : Primrec (fun q : P => q.1.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have h2 : Primrec (fun q : P => q.1.1.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have h3 : Primrec (fun q : P => q.1.2) := Primrec.snd.comp Primrec.fst
  have h4 : Primrec (fun q : P => q.2) := Primrec.snd
  have h := defaultSyntaxApplicationPrimitiveRecursive.comp (h1.pair (h2.pair (h3.pair h4)))
  exact h.of_eq (fun q => rfl)

private theorem lamBindPrimitive : Primrec (fun p : Nat×Nat×Option (List Nat) =>
    p.2.2.bind (fun b => abstractionCode p.1 p.2.1 b)) := by
  apply Primrec.option_bind (Primrec.snd.comp Primrec.snd)
  exact ordinalSyntaxAbstractionPrimitiveRecursive.comp
    ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))

theorem assignmentPrimitiveRecursive : Targets.AssignmentPrimitiveRecursive := by
  let S := List Nat×Nat
  let children : S → List S := fun s =>
    if s.2%8=5 then [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
    else if s.2%8=6 then [((s.2/8).unpair.1::s.1,(s.2/8).unpair.2)] else []
  let finish : S×List (Option (List Nat)) → Nat → Option (List Nat) := fun p resultType =>
    if p.1.2%8<5 then some (primeCode (p.1.2%8) (p.1.2/8) (typeLevel resultType))
    else if p.1.2%8=5 then (check p.1.1 (p.1.2/8).unpair.2).bind (fun argType =>
      (p.2.getD 0 none).bind (fun f => (p.2.getD 1 none).map (fun a =>
        defaultApplicationCode (typeLevel resultType) (typeLevel argType) f a)))
    else if p.1.2%8=6 then (check ((p.1.2/8).unpair.1::p.1.1) (p.1.2/8).unpair.2).bind (fun bodyType =>
      (p.2.getD 0 none).bind (fun b => abstractionCode (typeLevel (p.1.2/8).unpair.1) (typeLevel bodyType) b))
    else none
  let assemble : S → List (Option (List Nat)) → Option (Option (List Nat)) := fun s rs =>
    some ((check s.1 s.2).bind (finish (s,rs)))
  have htag : Primrec (fun s : S => s.2%8) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  have hpay : Primrec (fun s : S => s.2/8) := Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : S => s.2%8=k) := Primrec.eq.comp htag (Primrec.const k)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 6)
      (Primrec.list_cons.comp ((Primrec.list_cons.comp hl Primrec.fst).pair hr) (Primrec.const []))
      (Primrec.const []))
  have hf : Primrec₂ finish := by
    let P := (S×List (Option (List Nat)))×Nat
    have hs : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
    have ht' := htag.comp hs
    have hp' := hpay.comp hs
    have hl' := hl.comp hs
    have hr' := hr.comp hs
    have hg (k : Nat) : Primrec (fun p : P => p.1.2.getD k none) :=
      (Primrec.list_getD (none : Option (List Nat))).comp (Primrec.snd.comp Primrec.fst) (Primrec.const k)
    have level : Primrec typeLevel := SyntaxCode.StatementChecks.typeLevelPrimitiveRecursive
    have happ : Primrec (fun p : P => (check p.1.1.1 (p.1.1.2/8).unpair.2).bind (fun a =>
      (p.1.2.getD 0 none).bind (fun f => (p.1.2.getD 1 none).map (fun b =>
        defaultApplicationCode (typeLevel p.2) (typeLevel a) f b)))) := by
      apply Primrec.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp
        ((Primrec.fst.comp hs).pair hr'))
      exact appBindPrimitive.comp ((level.comp (Primrec.snd.comp Primrec.fst)).pair
        ((level.comp Primrec.snd).pair (((hg 0).comp Primrec.fst).pair ((hg 1).comp Primrec.fst))))
    have hlam : Primrec (fun p : P => (check ((p.1.1.2/8).unpair.1::p.1.1.1) (p.1.1.2/8).unpair.2).bind (fun a =>
      (p.1.2.getD 0 none).bind (fun b => abstractionCode (typeLevel (p.1.1.2/8).unpair.1) (typeLevel a) b))) := by
      apply Primrec.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp
        ((Primrec.list_cons.comp hl' (Primrec.fst.comp hs)).pair hr'))
      change Primrec (fun q : P×Nat =>
        (q.1.1.2.getD 0 none).bind (fun b =>
          abstractionCode (typeLevel (q.1.1.1.2/8).unpair.1) (typeLevel q.2) b))
      have h1 : Primrec (fun q : P×Nat => typeLevel (q.1.1.1.2/8).unpair.1) :=
        (level.comp hl').comp Primrec.fst
      have h2 : Primrec (fun q : P×Nat => typeLevel q.2) := level.comp Primrec.snd
      have h3 : Primrec (fun q : P×Nat => q.1.1.2.getD 0 none) := (hg 0).comp Primrec.fst
      have hh := lamBindPrimitive.comp (h1.pair (h2.pair h3))
      exact hh.of_eq (fun q => rfl)
    exact Primrec.ite (Primrec.nat_lt.comp ht' (Primrec.const 5))
      (Primrec.option_some.comp (primeCodePrimitiveRecursive.comp (ht'.pair (hp'.pair (level.comp Primrec.snd)))))
      (Primrec.ite ((ht 5).comp hs) happ (Primrec.ite ((ht 6).comp hs) hlam (Primrec.const none)))
  have ha : Primrec₂ assemble := Primrec.option_some.comp
    (Primrec.option_bind (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp Primrec.fst) hf)
  apply Primrec.nat_omega_rec' (fun s : S => assignmentCode s.1 s.2) Primrec.snd hc ha
  · intro s t hmem
    change t.2 < s.2
    by_cases h5 : s.2%8=5
    · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2%8=6
      · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hmem
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hmem
  · intro s
    conv_rhs => rw [assignmentCode]
    have ht : s.2%8=0 ∨ s.2%8=1 ∨ s.2%8=2 ∨ s.2%8=3 ∨ s.2%8=4 ∨ s.2%8=5 ∨ s.2%8=6 ∨ s.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,finish,h,Option.bind_assoc]

    have map_bind {α β : Type} (f : α → β) (x : Option α) :
        x.map f = x.bind (fun a => some (f a)) := by cases x <;> rfl
    simp only [map_bind]

theorem assignmentComputable : Targets.AssignmentComputable := assignmentPrimitiveRecursive.to_comp
end LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.Proof
