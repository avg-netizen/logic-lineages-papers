module
public import LogicLineages.OrdinalComparison.MultivariatePhiCounterTargets
public import LogicLineages.OrdinalComparison.MultivariateIdentityDecisionProof
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariatePhiCounter

attribute [local irreducible] Phi actualCollapse encodedMultivariateCounterWeight encodedPositiveZeroBound
attribute [local irreducible] encodedMultivariateCounterRayStep

private theorem weighted_value (w : Nat → Nat) (E : MultivariatePositiveExpr) (x : Nat) :
    actualFixedLimitProfileEval (multivariatePositiveWeightedRay w E) x=
      actualMultivariatePositiveEval E (fun i => w i*x) := by
  induction E with
  | constant c => rfl
  | input i => exact MultivariatePositiveRay.source.2.1 _ _
  | add E F ihE ihF => exact congrArg₂ (·+·) ihE ihF
  | head rho E ih => exact congrArg (actualProfileHead rho) ih

private theorem weighted_valid (d : Nat) (w : Nat → Nat) (E : MultivariatePositiveExpr)
    (hv : multivariatePositiveValid d E) :
    fixedLimitProfileBelow epsilonZero (multivariatePositiveWeightedRay w E) := by
  induction E with
  | constant c => trivial
  | input i => exact MultivariatePositiveRay.source.2.2.1 _
  | add E F ihE ihF => exact ⟨ihE hv.1,ihF hv.2⟩
  | head rho E ih => exact ⟨hv.1,hv.2.1,ih hv.2.2⟩

theorem source : Targets.MultivariateWeightedRaySource := ⟨weighted_value,weighted_valid⟩

private theorem computable_ite {α σ : Type} [Primcodable α] [Primcodable σ]
    {p : α → Prop} [DecidablePred p] {f g : α → σ}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

private theorem step_computable : Computable (fun p : (Nat × Nat) × (Nat × List Nat) =>
    encodedMultivariateCounterRayStep p.1.1 p.1.2 p.2.1 p.2.2) := by
  unfold encodedMultivariateCounterRayStep
  have hn : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hc : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hmod := Primrec.nat_mod.comp hc (Primrec.const 4)
  have hd := Primrec.nat_div.comp hc (Primrec.const 4)
  have hp := Primrec.unpair.comp hd
  have hl := Primrec.fst.comp hp
  have hr := Primrec.snd.comp hp
  have hvL := (Primrec.list_getD 0).comp ht hl
  have hvR := (Primrec.list_getD 0).comp ht hr
  have hw := MultivariateIdentityDecision.weight_computable.comp
    (hn.to_comp.pair (hm.to_comp.pair hd.to_comp))
  exact computable_ite (Primrec.eq.comp hmod (Primrec.const 0)) hc.to_comp
    (computable_ite (Primrec.eq.comp hmod (Primrec.const 1))
      (MultivariatePositiveRay.code.1.to_comp.comp hw)
      (computable_ite (Primrec.eq.comp hmod (Primrec.const 2))
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec₂.natPair.comp hvL hvR)) (Primrec.const 2)).to_comp
        (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4)
          (Primrec₂.natPair.comp hl hvR)) (Primrec.const 3)).to_comp))

private noncomputable def tableProgram (p : Nat × Nat) (c : Nat) : List Nat :=
  Nat.rec [] (fun k table => table ++ [encodedMultivariateCounterRayStep p.1 p.2 k table]) c

private theorem table_program_unfold (p : Nat × Nat) (c : Nat) :
    tableProgram p c=Nat.rec []
      (fun k table => table ++ [encodedMultivariateCounterRayStep p.1 p.2 k table]) c := rfl

private theorem table_program_eq (n m c : Nat) :
    tableProgram (n,m) c=encodedMultivariateCounterRayTable n m c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    change tableProgram (n,m) c ++ [encodedMultivariateCounterRayStep n m c (tableProgram (n,m) c)]=
      encodedMultivariateCounterRayTable n m c ++
        [encodedMultivariateCounterRayStep n m c (encodedMultivariateCounterRayTable n m c)]
    rw [ih]

private theorem append_computable : Computable (fun p : (Nat × Nat) × (Nat × List Nat) =>
    p.2.2 ++ [encodedMultivariateCounterRayStep p.1.1 p.1.2 p.2.1 p.2.2]) :=
  Computable.list_concat.comp (Computable.snd.comp Computable.snd) step_computable

private theorem lifted_append_computable :
    Computable (fun z : ((Nat × Nat) × Nat) × (Nat × List Nat) =>
      z.2.2 ++ [encodedMultivariateCounterRayStep z.1.1.1 z.1.1.2 z.2.1 z.2.2]) := by
  have hp : Computable (fun z : ((Nat × Nat) × Nat) × (Nat × List Nat) =>
      (z.1.1,z.2)) :=
    (Computable.fst.comp Computable.fst).pair Computable.snd
  exact Computable.comp
    (α := ((Nat × Nat) × Nat) × (Nat × List Nat))
    (β := (Nat × Nat) × (Nat × List Nat)) (σ := List Nat)
    (f := fun p => p.2.2 ++ [encodedMultivariateCounterRayStep p.1.1 p.1.2 p.2.1 p.2.2])
    (g := fun z => (z.1.1,z.2)) append_computable hp

attribute [local irreducible] tableProgram

private theorem table_program_computable : Computable (fun p : (Nat × Nat) × Nat =>
    tableProgram p.1 p.2) := by
  have h : Computable (fun p : (Nat × Nat) × Nat => Nat.rec (motive := fun _ => List Nat) []
      (fun k table => table ++ [encodedMultivariateCounterRayStep p.1.1 p.1.2 k table]) p.2) :=
    Computable.nat_rec (α := (Nat × Nat) × Nat) (σ := List Nat)
      (f := fun p => p.2) (g := fun _ => [])
      (h := fun p q => q.2 ++ [encodedMultivariateCounterRayStep p.1.1 p.1.2 q.1 q.2])
      Computable.snd (Computable.const ([] : List Nat)) lifted_append_computable
  exact h.of_eq (fun p => (table_program_unfold p.1 p.2).symm)

attribute [local irreducible] encodedMultivariateCounterRayTable

private theorem table_computable : Computable (fun p : (Nat × Nat) × Nat =>
    encodedMultivariateCounterRayTable p.1.1 p.1.2 p.2) :=
  table_program_computable.of_eq (fun p => table_program_eq p.1.1 p.1.2 p.2)

theorem ray_computable :
    Computable (fun p : Nat × Nat × Nat => encodedMultivariateCounterRay p.1 p.2.1 p.2.2) := by
  have hparam : Computable (fun p : Nat × Nat × Nat => (p.1,p.2.1)) :=
    Computable.fst.pair (Computable.fst.comp Computable.snd)
  have hc : Computable (fun p : Nat × Nat × Nat => p.2.2) := Computable.snd.comp Computable.snd
  exact (Primrec.list_getD 0).to_comp.comp
    (table_computable.comp (hparam.pair (Primrec.succ.to_comp.comp hc))) hc

private theorem table_length (n m c : Nat) :
    (encodedMultivariateCounterRayTable n m c).length=c := by
  induction c with
  | zero => simp only [encodedMultivariateCounterRayTable,List.length_nil]
  | succ c ih => simp [encodedMultivariateCounterRayTable,ih]

private theorem step_correct (n m : Nat) (E : MultivariatePositiveExpr) (table : List Nat)
    (ht : ∀ F : MultivariatePositiveExpr, multivariatePositiveEncode F<multivariatePositiveEncode E →
      table.getD (multivariatePositiveEncode F) 0=
        positiveExprEncode (multivariatePositiveWeightedRay (encodedMultivariateCounterWeight n m) F)) :
    encodedMultivariateCounterRayStep n m (multivariatePositiveEncode E) table=
      positiveExprEncode (multivariatePositiveWeightedRay (encodedMultivariateCounterWeight n m) E) := by
  cases E with
  | constant c =>
    have hm : (4*c)%4=0 := by omega
    simp [multivariatePositiveEncode,encodedMultivariateCounterRayStep,multivariatePositiveWeightedRay,positiveExprEncode,hm]
  | input i =>
    have hm : (4*i+1)%4=1 := by omega
    have hd : (4*i+1)/4=i := by omega
    simp only [multivariatePositiveEncode,encodedMultivariateCounterRayStep,hm,hd]
    norm_num only
    exact MultivariatePositiveRay.source.1 _
  | add E F =>
    let a := multivariatePositiveEncode E
    let b := multivariatePositiveEncode F
    have ha : a<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.left_le_pair a b) (by omega)
    have hb : b<4*Nat.pair a b+2 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E ha
    have hF := ht F hb
    have hm : (4*Nat.pair a b+2)%4=2 := by omega
    have hd : (4*Nat.pair a b+2)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [multivariatePositiveEncode,encodedMultivariateCounterRayStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE,hF]
    rfl
  | head rho E =>
    let a := rawNoteEncode rho.1
    let b := multivariatePositiveEncode E
    have hb : b<4*Nat.pair a b+3 := lt_of_le_of_lt (Nat.right_le_pair a b) (by omega)
    have hE := ht E hb
    have hm : (4*Nat.pair a b+3)%4=3 := by omega
    have hd : (4*Nat.pair a b+3)/4=Nat.pair a b := by omega
    dsimp only [a,b] at hm hd
    simp only [multivariatePositiveEncode,encodedMultivariateCounterRayStep,hm,hd,Nat.unpair_pair]
    norm_num only
    rw [hE]
    rfl

private theorem table_correct (n m c : Nat) : ∀ E : MultivariatePositiveExpr,
    multivariatePositiveEncode E<c →
    (encodedMultivariateCounterRayTable n m c).getD (multivariatePositiveEncode E) 0=
      positiveExprEncode (multivariatePositiveWeightedRay (encodedMultivariateCounterWeight n m) E) := by
  induction c with
  | zero => intro E h; omega
  | succ c ih =>
    intro E hE
    by_cases heq : multivariatePositiveEncode E=c
    · rw [encodedMultivariateCounterRayTable,List.getD_append_right _ _ _ _
        (by rw [table_length]; omega)]
      rw [table_length,heq,Nat.sub_self]
      change encodedMultivariateCounterRayStep n m c _=_
      simpa only [heq] using step_correct n m E (encodedMultivariateCounterRayTable n m c)
        (fun F hF => ih F (by omega))
    · rw [encodedMultivariateCounterRayTable,List.getD_append _ _ _ _
        (by rw [table_length]; omega)]
      exact ih E (by omega)

theorem ray_correct (n m : Nat) (E : MultivariatePositiveExpr) :
    encodedMultivariateCounterRay n m (multivariatePositiveEncode E)=
      positiveExprEncode (multivariatePositiveWeightedRay (encodedMultivariateCounterWeight n m) E) :=
  table_correct n m (multivariatePositiveEncode E+1) E (Nat.lt_succ_self _)

theorem code : Targets.MultivariateCounterRayCode := ⟨ray_computable,ray_correct⟩

attribute [local irreducible] encodedMultivariateCounterRay

theorem index_computable : Computable₂ encodedMultivariatePhiCounterIndex := by
  have hn : Computable (fun p : Nat × Nat => p.1) := Computable.fst
  have hm : Computable (fun p : Nat × Nat => p.2) := Computable.snd
  have hleft : Computable (fun p : Nat × Nat => encodedMultivariateCounterRay p.1 p.2 p.1) :=
    ray_computable.comp (hn.pair (hm.pair hn))
  have hright : Computable (fun p : Nat × Nat => encodedMultivariateCounterRay p.1 p.2 p.2) :=
    ray_computable.comp (hn.pair (hm.pair hm))
  exact fullActualPositiveFiniteZeros.1.comp hleft hright

theorem phi_counter : Targets.MultivariatePhiRayCounter := by
  refine ⟨index_computable,?_⟩
  intro d E F hE hF
  let n := multivariatePositiveEncode E
  let m := multivariatePositiveEncode F
  let w := encodedMultivariateCounterWeight n m
  let PE := multivariatePositiveWeightedRay w E
  let PF := multivariatePositiveWeightedRay w F
  let k := encodedMultivariatePhiCounterIndex n m
  change encodedMultivariateIdentity n m=false → _
  intro hfalse
  have hpE : fixedLimitProfileBelow epsilonZero PE := source.2 d w E hE
  have hpF : fixedLimitProfileBelow epsilonZero PF := source.2 d w F hF
  have hk : k=encodedPositiveZeroBound (positiveExprEncode PE) (positiveExprEncode PF) := by
    dsimp only [k,encodedMultivariatePhiCounterIndex]
    rw [ray_correct n m E,ray_correct n m F]
  have hw := (MultivariateIdentityDecision.decision.2.2.2 d E F hE hF).2 hfalse
  have hdiff : actualFixedLimitProfileEval PE 1≠actualFixedLimitProfileEval PF 1 := by
    change actualFixedLimitProfileEval (multivariatePositiveWeightedRay w E) 1≠
      actualFixedLimitProfileEval (multivariatePositiveWeightedRay w F) 1
    simpa only [weighted_value,Nat.mul_one] using hw.2
  have hz := fullActualPositiveFiniteZeros.2.2 PE PF hpE hpF
  have hnf : collectedPositiveNormalize PE≠collectedPositiveNormalize PF := by
    intro heq
    exact hdiff (hz.2.1 heq 1)
  have hkv : encodedPositiveZeroBound (positiveExprEncode PE) (positiveExprEncode PF)≤Phi k+1 := by
    have hg := self_lt_Phi k
    omega
  refine ⟨?_,hw.1,?_⟩
  · change 1≤k
    rw [hk]
    exact hz.1
  · have hne := (hz.2.2.1 hnf).1 (Phi k+1) hkv
    change actualFixedLimitProfileEval (multivariatePositiveWeightedRay w E) (Phi k+1)≠
      actualFixedLimitProfileEval (multivariatePositiveWeightedRay w F) (Phi k+1) at hne
    simpa only [weighted_value] using hne

end LogicLineages.OrdinalComparison.MultivariatePhiCounter
