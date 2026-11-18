module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.Targets
public import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.HeadProgramsProof
public import LogicLineages.OrdinalComparison.PolynomialGraphCompletion.ExpressionCodeProgramsProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.ProgramsProof
open OrdinalComparison PolynomialGraphCompletion
open LayeredComparison.IntegerAlgorithms.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

/-- Numeric constructors retain the literal formula encoding. -/
theorem nonnegative_primitive : Primrec Code.nonnegative :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6)
      (Primrec.encode.comp ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id))))
    (Primrec.const 2)

theorem neg_primitive : Primrec Code.neg :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec.id) (Primrec.const 3)

theorem conj_primitive : Primrec₂ Code.conj :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 4)

theorem disj_primitive : Primrec₂ Code.disj :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 5)

theorem negativeRow_primitive : Primrec negativeRow := by
  have hm : Primrec (fun r : Row => r.2.map (fun a => (-a.1,a.2))) :=
    Primrec.list_map Primrec.snd
      ((negate_primitive.comp (Primrec.fst.comp Primrec.snd)).pair
        (Primrec.snd.comp Primrec.snd)).to₂
  exact (negate_primitive.comp Primrec.fst).pair hm

theorem equal_primitive : Primrec Code.equal :=
  conj_primitive.comp nonnegative_primitive
    (nonnegative_primitive.comp negativeRow_primitive)

theorem graph_primitive : Primrec Code.graph :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (conj_primitive.comp (equal_primitive.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂


theorem relationRow_primitive : Primrec (fun p : Bool × Nat × Nat => relationRow p.1 p.2.1 p.2.2) := by
  have hc : Primrec (fun p : Bool × Nat × Nat => if p.1 then (-1 : Int) else 0) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true)) (Primrec.const (-1)) (Primrec.const 0)
  exact hc.pair (Primrec.list_cons.comp
    ((Primrec.const (1 : Int)).pair ((Primrec.snd.comp Primrec.snd).pair (Primrec.const [])))
    (Primrec.list_cons.comp
      ((Primrec.const (-1 : Int)).pair ((Primrec.fst.comp Primrec.snd).pair (Primrec.const [])))
      (Primrec.const [])))

theorem test_primitive : Primrec (fun p : Nat × Nat × Nat => Code.test p.1 p.2.1 p.2.2) := by
  have rowFalse : Primrec (fun p : Nat × Nat × Nat => relationRow false p.2.1 p.2.2) :=
    relationRow_primitive.comp ((Primrec.const false).pair Primrec.snd)
  have hb : Primrec (fun p : Nat × Nat × Nat => p.1 != 1) :=
    Primrec.not.comp (Primrec.beq.comp Primrec.fst (Primrec.const 1))
  have rowStrict : Primrec (fun p : Nat × Nat × Nat => relationRow (p.1 != 1) p.2.1 p.2.2) :=
    relationRow_primitive.comp (hb.pair Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (equal_primitive.comp rowFalse) (nonnegative_primitive.comp rowStrict)

theorem positive_primitive : Primrec Code.positive := by
  have hr : Primrec (fun i : Nat => ((-1 : Int),[((1 : Int),i,([] : Word))])) :=
    (Primrec.const (-1 : Int)).pair (Primrec.list_cons.comp
      ((Primrec.const (1 : Int)).pair (Primrec.id.pair (Primrec.const []))) (Primrec.const []))
  exact Primrec.list_foldr Primrec.list_range (Primrec.const 0)
    (conj_primitive.comp (nonnegative_primitive.comp (hr.comp (Primrec.fst.comp Primrec.snd)))
      (Primrec.snd.comp Primrec.snd)).to₂

theorem step_primitive : Primrec₂ Code.step := by
  let A := Code.State × Instruction
  have hn : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hr : Primrec (fun p : A => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ht : Primrec (fun p : A => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have htag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hleft : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hright : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have htop : Primrec (fun p : A => p.1.2.2.headD 1) :=
    Primrec.option_getD.comp (Primrec.list_head?.comp ht) (Primrec.const 1)
  have hnext : Primrec (fun p : A => p.1.2.2.getD 1 1) :=
    (Primrec.list_getD (1 : Nat)).comp ht (Primrec.const 1)
  have hdrop : Primrec (fun p : A => p.1.2.2.drop 2) :=
    Primrec.list_drop.comp (Primrec.const 2) ht
  have htruth : Primrec (fun p : A =>
      (p.1.1,p.1.2.1,(if p.2.1=1 then 0 else 1)::p.1.2.2)) :=
    hn.pair (hr.pair (Primrec.list_cons.comp
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 1)) (Primrec.const 0) (Primrec.const 1)) ht))
  let first (p : A) := ExpressionCode.run (ExpressionCode.instructions p.2.2.1) (p.1.1,[],[])
  have ha : Primrec first := ExpressionCodeProgramsProof.run_primitive.comp
    (ExpressionCodeProgramsProof.instructions_primitive.comp hleft)
    (hn.pair ((Primrec.const []).pair (Primrec.const [])))
  let second (p : A) := ExpressionCode.run (ExpressionCode.instructions p.2.2.2) ((first p).1,[],[])
  have hb : Primrec second := ExpressionCodeProgramsProof.run_primitive.comp
    (ExpressionCodeProgramsProof.instructions_primitive.comp hright)
    ((Primrec.fst.comp ha).pair ((Primrec.const []).pair (Primrec.const [])))
  have hatop : Primrec (fun p : A => (first p).2.1.headD 0) :=
    Primrec.option_getD.comp (Primrec.list_head?.comp (Primrec.fst.comp (Primrec.snd.comp ha))) (Primrec.const 0)
  have hbtop : Primrec (fun p : A => (second p).2.1.headD 0) :=
    Primrec.option_getD.comp (Primrec.list_head?.comp (Primrec.fst.comp (Primrec.snd.comp hb))) (Primrec.const 0)
  have hatom : Primrec (fun p : A =>
      ((second p).1,p.1.2.1++(first p).2.2++(second p).2.2,
       Code.test (p.2.1-2) ((first p).2.1.headD 0) ((second p).2.1.headD 0)::p.1.2.2)) :=
    (Primrec.fst.comp hb).pair
      ((Primrec.list_append.comp
        (Primrec.list_append.comp hr (Primrec.snd.comp (Primrec.snd.comp ha)))
        (Primrec.snd.comp (Primrec.snd.comp hb))).pair
       (Primrec.list_cons.comp
         (test_primitive.comp ((Primrec.nat_sub.comp htag (Primrec.const 2)).pair (hatop.pair hbtop))) ht))
  have hneg : Primrec (fun p : A => (p.1.1,p.1.2.1,Code.neg (p.1.2.2.headD 1)::p.1.2.2.tail)) :=
    hn.pair (hr.pair (Primrec.list_cons.comp (neg_primitive.comp htop) (Primrec.list_tail.comp ht)))
  have hconj : Primrec (fun p : A =>
      (p.1.1,p.1.2.1,Code.conj (p.1.2.2.getD 1 1) (p.1.2.2.headD 1)::p.1.2.2.drop 2)) :=
    hn.pair (hr.pair (Primrec.list_cons.comp (conj_primitive.comp hnext htop) hdrop))
  have hdisj : Primrec (fun p : A =>
      (p.1.1,p.1.2.1,Code.disj (p.1.2.2.getD 1 1) (p.1.2.2.headD 1)::p.1.2.2.drop 2)) :=
    hn.pair (hr.pair (Primrec.list_cons.comp (disj_primitive.comp hnext htop) hdrop))
  exact Primrec.ite (Primrec.nat_le.comp htag (Primrec.const 1)) htruth
    (Primrec.ite (Primrec.nat_le.comp htag (Primrec.const 4)) hatom
      (Primrec.ite (Primrec.eq.comp htag (Primrec.const 5)) hneg
        (Primrec.ite (Primrec.eq.comp htag (Primrec.const 6)) hconj hdisj)))

theorem decode_primitive : Primrec Code.decode :=
  Primrec.option_getD.comp Primrec.decode (Primrec.const [])

theorem heads_primitive : Primrec Code.heads := by
  let A := List Instruction × Instruction
  have htag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have ha : Primrec (fun p : A => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hb : Primrec (fun p : A => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_flatMap Primrec.id
    (Primrec.ite ((Primrec.nat_le.comp (Primrec.const 2) htag).and
        (Primrec.nat_le.comp htag (Primrec.const 4)))
      (Primrec.list_append.comp
        (ExpressionCodeProgramsProof.headNames_primitive.comp
          (ExpressionCodeProgramsProof.instructions_primitive.comp ha))
        (ExpressionCodeProgramsProof.headNames_primitive.comp
          (ExpressionCodeProgramsProof.instructions_primitive.comp hb)))
      (Primrec.const [])).to₂

theorem run_primitive : Primrec (fun p : Nat × List Instruction =>
    p.2.foldl Code.step (p.1,[],[])) :=
  Primrec.list_foldl Primrec.snd
    (Primrec.fst.pair ((Primrec.const []).pair (Primrec.const [])))
    (step_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

theorem package_primitive : Primrec (fun p : Nat × Nat => Code.package p.1 p.2) := by
  have hops : Primrec (fun p : Nat × Nat => Code.decode p.2) := decode_primitive.comp Primrec.snd
  have hs : Primrec (fun p : Nat × Nat => (Code.decode p.2).foldl Code.step (p.1,[],[])) :=
    run_primitive.comp (Primrec.fst.pair hops)
  have hd : Primrec (fun p : Nat × Nat => familyDegree (Code.heads (Code.decode p.2))) :=
    HeadProgramsProof.familyDegree_primitive.comp (heads_primitive.comp hops)
  have hp : Primrec (fun p : Nat × Nat => Code.positive p.1) := positive_primitive.comp Primrec.fst
  have hg : Primrec (fun p : Nat × Nat =>
      Code.graph ((Code.decode p.2).foldl Code.step (p.1,[],[])).2.1) :=
    graph_primitive.comp (Primrec.fst.comp (Primrec.snd.comp hs))
  have ho : Primrec (fun p : Nat × Nat =>
      ((Code.decode p.2).foldl Code.step (p.1,[],[])).2.2.headD 1) :=
    Primrec.option_getD.comp (Primrec.list_head?.comp (Primrec.snd.comp (Primrec.snd.comp hs))) (Primrec.const 1)
  exact hd.pair ((Primrec.fst.comp hs).pair
    ((conj_primitive.comp hp (conj_primitive.comp hg ho)).pair
      (conj_primitive.comp hp (conj_primitive.comp hg (neg_primitive.comp ho)))))

end LogicLineages.StandardControlCurrent.PolynomialBoolean.ProgramsProof
