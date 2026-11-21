module
public import LogicLineages.PermittedControl.CountCongruenceNamedRowTargets
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.CountCongruenceNamedRow
open OrdinalComparison FieldComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof

private theorem normPrimitive : Primrec rawNormCode :=
  Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive

private theorem countPrimitive :
    Primrec (fun p : Nat × Nat × Nat => residueCount p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Nat
  have hk : Primrec (fun p : A => p.1) := Primrec.fst
  have hn : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hj : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hhalf := ofNat_primitive.comp (Primrec.nat_div.comp hj (Primrec.const 2))
  have hc := ofNat_primitive.comp
    (Primrec.nat_div.comp (Primrec.succ.comp hn) (Primrec.const 2))
  have hd : Primrec (fun p : A => ((p.2.2/2 : Nat) : Int) -
      (((p.2.1+1)/2 : Nat) : Int)) := by
    simpa only [sub_eq_add_neg] using (add_primitive.comp hhalf (negate_primitive.comp hc))
  exact Primrec.ite (Primrec.eq.comp hk (Primrec.const 0)) hd (ofNat_primitive.comp hk)

private abbrev RowArgs := Nat × Nat × Nat × Int × Int × Int
private abbrev TestArgs := RowArgs × Nat

private theorem keepPrimitive :
    Primrec (fun p : TestArgs =>
      keepResidue p.1.1 p.1.2.1 p.1.2.2.1 p.2 p.1.2.2.2.1 p.1.2.2.2.2.1 p.1.2.2.2.2.2) := by
  have hm : Primrec (fun p : TestArgs => p.1.1) := Primrec.fst.comp Primrec.fst
  have ht : Primrec (fun p : TestArgs => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hk : Primrec (fun p : TestArgs => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hn := Primrec.fst.comp ht
  have hcs := Primrec.snd.comp ht
  have hc := Primrec.fst.comp hcs
  have hu := Primrec.fst.comp (Primrec.snd.comp hcs)
  have hv := Primrec.snd.comp (Primrec.snd.comp hcs)
  have hd := countPrimitive.comp (hk.pair (hn.pair Primrec.snd))
  have hx := mul_primitive.comp hu (ofNat_primitive.comp (Primrec.snd : Primrec (fun p : TestArgs => p.2)))
  have hr := mul_primitive.comp hv hd
  have hsum := add_primitive.comp (add_primitive.comp hc hx) hr
  exact (Primrec.eq.comp (Primrec.nat_mod.comp (abs_primitive.comp hsum) hm) (Primrec.const 0)).decide

private theorem atomPrimitive : Primrec₂ residueAtomCode := by
  let A := Nat × Nat
  have hm : Primrec (fun p : A => 2*p.1-1) :=
    Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) (Primrec.const 1)
  have hj : Primrec (fun p : A => -(p.2 : Int)) :=
    negate_primitive.comp (ofNat_primitive.comp Primrec.snd)
  have hdata : Primrec (fun p : A =>
      ((1,2*p.1-1,(-(p.2 : Int),[(1,(0,1,0,0))])) : NormalForm.Code.AtomData)) :=
    (Primrec.const 1).pair (hm.pair (hj.pair (Primrec.const [(1,(0,1,0,0))])))
  exact Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6)
    (Primrec.encode.comp hdata)) (Primrec.const 2)

private theorem rowPrimitive :
    Primrec (fun p : RowArgs => rowCode p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) := by
  let A := RowArgs × (Nat × Nat)
  have hlist : Primrec (fun p : RowArgs => List.range (2*p.1)) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
  have hj : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hm : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hkeep := keepPrimitive.comp (Primrec.fst.pair hj)
  have hor := Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) (Primrec₂.natPair.comp (atomPrimitive.comp hm hj) ht))
    (Primrec.const 5)
  have hstep : Primrec (fun p : A =>
      if keepResidue p.1.1 p.1.2.1 p.1.2.2.1 p.2.1 p.1.2.2.2.1 p.1.2.2.2.2.1 p.1.2.2.2.2.2
      then 6 * Nat.pair (residueAtomCode p.1.1 p.2.1) p.2.2 + 5 else p.2.2) :=
    Primrec.ite (Primrec.eq.comp hkeep (Primrec.const true)) hor ht
  exact Primrec.list_foldr hlist (Primrec.const 1) hstep.to₂

private theorem preparePrimitive : Primrec prepareCode := by
  have hm : Primrec (fun p : RawArgs => p.1) := Primrec.fst
  have hr : Primrec (fun p : RawArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have hends : Primrec (fun p : RawArgs => p.2.2) := Primrec.snd.comp Primrec.snd
  have hl := Primrec.fst.comp hends
  have hrest := Primrec.snd.comp hends
  have hmu := Primrec.fst.comp hrest
  have hcs := Primrec.snd.comp hrest
  have hk := shortFieldPreprocessingEffective.2.1.comp hl hmu
  have hn := normPrimitive.comp hmu
  have hrow := rowPrimitive.comp (hm.pair (hk.pair (hn.pair hcs)))
  have hname : Primrec (fun p : RawArgs => ((1,(0,p.2.1,(0,0,0,0))) : NamedCode)) :=
    (Primrec.const 1).pair ((Primrec.const 0).pair (hr.pair (Primrec.const (0,0,0,0))))
  have htable := Primrec.list_cons.comp hname (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp hm (Primrec.const 0)) (Primrec.const none)
    (Primrec.option_some.comp (htable.pair hrow))

private theorem tailPrimitive :
    Primrec (fun z : Nat × Nat × Nat × Nat => tailCode z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  let A := Nat × Nat × Nat × Nat
  have hB : Primrec (fun p : A => p.1) := Primrec.fst
  have hl : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hmu : Primrec (fun p : A => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun p : A => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.nat_max.comp (normPrimitive.comp hl)
    (Primrec.nat_max.comp (Primrec.nat_add.comp (normPrimitive.comp hmu) (Primrec.const 3))
      (Primrec.nat_max.comp hm hB))

private theorem rowLiteral (m k nmu : Nat) (c u v : Int) :
    rowCode m k nmu c u v = (row m k nmu c u v).encode := by
  unfold rowCode row
  generalize List.range (2*m) = js
  induction js with
  | nil => rfl
  | cons j js ih =>
    simp only [List.foldr_cons]
    by_cases h : keepResidue m k nmu j c u v = true
    · simp only [if_pos h,NormalForm.Formula.encode,ih] <;> rfl
    · simp only [if_neg h,ih]

theorem codeExact : CodeExact := by
  refine ⟨preparePrimitive,tailPrimitive,?_,?_,?_⟩
  · intro q hz
    rcases q with ⟨m,rank,lam,mu,c,u,v⟩
    change m = 0 at hz
    simp [prepareCode,hz]
  · intro B m lam mu
    simp only [tailCode,normal_norm_code]
  · intro m rank lam mu c u v hm
    simp only [prepareCode,rawArgs,if_neg (Nat.ne_of_gt hm),normal_norm_code,
      requests,List.map_cons,List.map_nil,encodeRequest,LowerOperand.code]
    rw [rowLiteral] <;> rfl

end LogicLineages.PermittedControl.CountCongruenceNamedRow
