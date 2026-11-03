module
public import LogicLineages.OrdinalComparison.ActualArithmeticCodeTargets
public import LogicLineages.OrdinalComparison.ControlComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem tagged_pair_primitive (base tag : Nat) :
    Primrec (fun p : Nat×Nat=>base*Nat.pair p.1 p.2+tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair) (Primrec.const tag)
private theorem numeral_primitive : Primrec numeralCode := Primrec.nat_mul.comp (Primrec.const 4) Primrec.id
private theorem variable_primitive : Primrec variableCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec.id) (Primrec.const 1)
private theorem add_primitive : Primrec₂ addCode := tagged_pair_primitive 4 2
private theorem scale_primitive : Primrec₂ scaleCode := tagged_pair_primitive 4 3
private theorem eq_primitive : Primrec₂ eqCode := tagged_pair_primitive 8 2
private theorem le_primitive : Primrec₂ leCode := tagged_pair_primitive 8 3
private theorem and_primitive : Primrec₂ andCode := tagged_pair_primitive 8 5
private theorem or_primitive : Primrec₂ orCode := tagged_pair_primitive 8 6
private theorem exists_primitive : Primrec existsCode :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.id) (Primrec.const 7)
private theorem observation_primitive :
    Primrec (fun p : Nat×Nat×List Nat×Nat=>observationCode p.1 p.2.1 p.2.2.1 p.2.2.2) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec.encode) (Primrec.const 4)
private theorem conjunction_primitive : Primrec conjunctionCode :=
  Primrec.list_foldr Primrec.id (Primrec.const truthCode) (and_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
private theorem disjunction_primitive : Primrec disjunctionCode :=
  Primrec.list_foldr Primrec.id (Primrec.const falsityCode) (or_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂

private def liftStep (k : Nat) (xs : List Nat) : Nat :=
  let n := xs.length
  let p := (n/4).unpair
  if n%4=0 then n else if n%4=1 then variableCode (n/4+k)
  else if n%4=2 then addCode (xs.getD p.1 0) (xs.getD p.2 0)
  else scaleCode p.1 (xs.getD p.2 0)
private theorem lift_step_exact (k n : Nat) :
    liftStep k ((List.range n).map (liftCode k))=liftCode k n := by
  conv_rhs => rw [liftCode]
  simp only [liftStep,List.length_map,List.length_range]
  by_cases h0 : n%4=0
  · simp only [h0,if_true]
  by_cases h1 : n%4=1
  · simp only [h0,h1,if_false,if_true]
  have hd : n/4<n := Nat.div_lt_self (by omega) (by decide)
  have hl : (n/4).unpair.1<n := (Nat.unpair_left_le _).trans_lt hd
  have hr : (n/4).unpair.2<n := (Nat.unpair_right_le _).trans_lt hd
  simp only [h0,h1,if_false,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range hl,List.getElem?_range hr,Option.map_some,Option.getD_some]
private theorem lift_step_primitive : Primrec₂ liftStep := by
  have hn : Primrec (fun p : Nat×List Nat=>p.2.length) := Primrec.list_length.comp Primrec.snd
  have hm := Primrec.nat_mod.comp hn (Primrec.const 4)
  have hd := Primrec.nat_div.comp hn (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hvl := (Primrec.list_getD (0 : Nat)).comp Primrec.snd hl
  have hvr := (Primrec.list_getD (0 : Nat)).comp Primrec.snd hr
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) hn
    (Primrec.ite (Primrec.eq.comp hm (Primrec.const 1))
      (variable_primitive.comp (Primrec.nat_add.comp hd Primrec.fst))
      (Primrec.ite (Primrec.eq.comp hm (Primrec.const 2)) (add_primitive.comp hvl hvr)
        (scale_primitive.comp hl hvr)))
private theorem lift_primitive : Primrec₂ liftCode :=
  Primrec.nat_strong_rec _ (Primrec.option_some.comp lift_step_primitive).to₂
    (fun k n=>congrArg Option.some (lift_step_exact k n))

attribute [local irreducible] observationCode
private theorem successor_primitive : Primrec₂ successorCode :=
  observation_primitive.comp ((Primrec.const 1).pair
    ((Primrec.const (SyntaxCode.encodeTerm (successorProbe (Γ:=[Ty.ground]) .here))).pair
      ((Primrec.list_cons.comp Primrec.fst (Primrec.const [])).pair Primrec.snd)))
private theorem phi_finite_primitive : Primrec (fun p : Nat×Nat=>
    disjunctionCode ((List.range 4).map fun i=>
      andCode (eqCode p.1 (numeralCode i)) (eqCode p.2 (numeralCode (Phi i))))) := by
  have hentry : Primrec (fun p : (Nat×Nat)×Nat=>
      andCode (eqCode p.1.1 (numeralCode p.2)) (eqCode p.1.2 (numeralCode (Phi p.2)))) :=
    and_primitive.comp (eq_primitive.comp (Primrec.fst.comp Primrec.fst) (numeral_primitive.comp Primrec.snd))
      (eq_primitive.comp (Primrec.snd.comp Primrec.fst) (numeral_primitive.comp (Phi_primrec.comp Primrec.snd)))
  exact disjunction_primitive.comp (Primrec.list_map (Primrec.const (List.range 4)) hentry.to₂)
private theorem phi_primitive : Primrec₂ phiCode := by
  have ha : Primrec (fun p : Nat×Nat=>liftCode 1 p.1) := lift_primitive.comp (Primrec.const 1) Primrec.fst
  have hb : Primrec (fun p : Nat×Nat=>liftCode 1 p.2) := lift_primitive.comp (Primrec.const 1) Primrec.snd
  have he := eq_primitive.comp ha (Primrec.const (addCode (variableCode 0) (numeralCode 4)))
  have hs := successor_primitive.comp (Primrec.const (variableCode 0)) hb
  exact or_primitive.comp phi_finite_primitive (exists_primitive.comp (and_primitive.comp he hs))

attribute [local irreducible] phiCode
private abbrev S := Nat×Nat×Nat
private def chainChildren (p : S) : List S :=
  if p.1=0 then [] else [(p.1-1,variableCode 0,liftCode 1 p.2.2)]
private def chainAssemble (p : S) (rs : List Nat) : Option Nat := some
  (if p.1=0 then eqCode p.2.2 p.2.1 else
    existsCode (andCode (phiCode (liftCode 1 p.2.1) (variableCode 0)) (rs.getD 0 0)))
private theorem chain_children_primitive : Primrec chainChildren := by
  have hn : Primrec (fun p : S=>p.1) := Primrec.fst
  have hb : Primrec (fun p : S=>p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) (Primrec.const [])
    (Primrec.list_cons.comp ((Primrec.nat_sub.comp hn (Primrec.const 1)).pair
      ((Primrec.const (variableCode 0)).pair (lift_primitive.comp (Primrec.const 1) hb))) (Primrec.const []))
private theorem chain_assemble_primitive : Primrec₂ chainAssemble := by
  have hn : Primrec (fun p : S×List Nat=>p.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : S×List Nat=>p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb : Primrec (fun p : S×List Nat=>p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hphi := phi_primitive.comp (lift_primitive.comp (Primrec.const 1) ha) (Primrec.const (variableCode 0))
  have hr : Primrec (fun p : S×List Nat=>p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0)
  exact Primrec.option_some.comp (Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) (eq_primitive.comp hb ha)
    (exists_primitive.comp (and_primitive.comp hphi hr)))
private theorem chain_primitive : Primrec (fun p : S=>phiChainCode p.1 p.2.1 p.2.2) := by
  apply Primrec.nat_omega_rec' (fun p : S=>phiChainCode p.1 p.2.1 p.2.2) Primrec.fst
    chain_children_primitive chain_assemble_primitive
  · intro p q hq
    by_cases h : p.1=0
    · simp [chainChildren,h] at hq
    · simp only [chainChildren,if_neg h,List.mem_singleton] at hq
      subst q
      change p.1-1<p.1
      omega
  · rintro ⟨n,a,b⟩
    cases n with
    | zero => simp only [chainAssemble,if_true,phiChainCode]
    | succ n => simp only [chainAssemble,chainChildren,Nat.succ_ne_zero,if_false,Nat.succ_sub_one,
        List.map_cons,List.map_nil,List.getD_cons_zero,phiChainCode]

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms :=
  ⟨numeral_primitive,variable_primitive,add_primitive,scale_primitive,lift_primitive,eq_primitive,le_primitive,
    observation_primitive,and_primitive,or_primitive,exists_primitive,conjunction_primitive,disjunction_primitive,
    successor_primitive,phi_primitive,chain_primitive⟩
end LogicLineages.OrdinalComparison.Source.ActualHeadGraph.ArithmeticCode.Proof
