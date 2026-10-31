module
public import LogicLineages.OrdinalComparison.SourceOneUnitTargets
public import Mathlib.Tactic.Ring
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Proof
open AdmissibleAssignment

theorem free_add {Γ σ} (a b : OrdinalExpression (σ :: Γ)) :
    ordinalHeadFree (.add a b) = (ordinalHeadFree a && ordinalHeadFree b) := by
  unfold ordinalHeadFree
  rw [ordinalHeadOccurs]
  cases ordinalHeadOccurs a <;> cases ordinalHeadOccurs b <;> rfl

theorem size_free {Γ σ} (t : OrdinalExpression (σ :: Γ)) (ht : ordinalHeadFree t=true) :
    ordinalPartialSize t=1 := by rw [ordinalPartialSize.eq_def,ht]; rfl

theorem size_add_active {Γ σ} (a b : OrdinalExpression (σ :: Γ))
    (ht : ordinalHeadFree (.add a b)=false) :
    ordinalPartialSize (.add a b)=ordinalPartialSize a+ordinalPartialSize b+1 := by
  rw [ordinalPartialSize.eq_def,ht]
  rfl

theorem size_pos {Γ σ} (t : OrdinalExpression (σ :: Γ)) : 0 < ordinalPartialSize t := by
  induction t with
  | var c | zero | one | omega => rw [ordinalPartialSize.eq_def]; split <;> simp
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    rw [ordinalPartialSize.eq_def]
    split <;> simp_all <;> omega

theorem size_add_ge_right {Γ σ} (a b : OrdinalExpression (σ :: Γ)) :
    ordinalPartialSize b ≤ ordinalPartialSize (.add a b) := by
  cases h : ordinalHeadFree (.add a b) with
  | false => rw [size_add_active a b h]; omega
  | true =>
    have hb : ordinalHeadFree b=true := (Bool.and_eq_true_iff.mp ((free_add a b).symm.trans h)).2
    rw [size_free _ h,size_free _ hb]

def repeatPos {Γ} (n : Nat) (t : OrdinalExpression Γ) : OrdinalExpression Γ :=
  repeated OrdinalSyntax.defaultPolicy .scalarRepeat (n+1) t

theorem repeat_zero {Γ} (t : OrdinalExpression Γ) : repeatPos 0 t=t := rfl

theorem repeat_succ {Γ} (n : Nat) (t : OrdinalExpression Γ) :
    repeatPos (n+1) t=.add (repeatPos n t) t := rfl

theorem repeat_active {Γ σ} (t : OrdinalExpression (σ :: Γ))
    (ht : ordinalHeadFree t=false) (n : Nat) : ordinalHeadFree (repeatPos n t)=false := by
  induction n with
  | zero => exact ht
  | succ n ih => rw [repeat_succ,free_add,ih]; rfl

theorem repeat_size {Γ σ} (t : OrdinalExpression (σ :: Γ))
    (ht : ordinalHeadFree t=false) (n : Nat) :
    ordinalPartialSize (repeatPos n t)=(n+1)*ordinalPartialSize t+n := by
  induction n with
  | zero => simp only [repeat_zero,Nat.zero_add,Nat.one_mul,Nat.add_zero]
  | succ n ih =>
    rw [repeat_succ,size_add_active _ _ (by rw [free_add,repeat_active t ht n]; rfl),ih]
    ring

def addPartial {Γ σ} (a b : OrdinalPartialVector Γ σ) : OrdinalPartialVector Γ σ :=
  fun j => .add (.add (a j) (b j)) .one

def repeatPartial {Γ σ} : Nat → OrdinalPartialVector Γ σ → OrdinalPartialVector Γ σ
  | 0,p => p
  | n+1,p => addPartial (repeatPartial n p) p

theorem run_add {Γ σ} (a b : OrdinalExpression (σ :: Γ))
    (ha : ordinalHeadFree a=false) (pa pb : OrdinalPartialVector Γ σ)
    (hpa : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 a=some pa)
    (hpb : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 b=some pb) :
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (.add a b)=some (addPartial pa pb) := by
  rw [AdmissiblePartial.run.eq_def,free_add,ha]
  simp only [Bool.false_and,Bool.false_eq_true,↓reduceIte,hpa,hpb,Option.bind_some]
  rfl

theorem run_repeat {Γ σ} (t : OrdinalExpression (σ :: Γ))
    (ht : ordinalHeadFree t=false) (p : OrdinalPartialVector Γ σ)
    (hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 t=some p) (n : Nat) :
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (repeatPos n t)=some (repeatPartial n p) := by
  induction n with
  | zero => exact hp
  | succ n ih => rw [repeat_succ]; exact run_add _ _ (repeat_active t ht n) _ _ ih hp

theorem inflated_size {Γ σ} (τ : Ty) (t : OrdinalExpression (σ :: Γ))
    (ht : ordinalHeadFree t=false) :
    ordinalPartialSize (inflated τ t)=coefficient τ*ordinalPartialSize t+3*copies τ := by
  have hk : 0 < copies τ := by unfold copies; omega
  have hk' : copies τ=(copies τ-1)+1 := by omega
  have hp : ordinalHeadFree (.add t .one)=false := by rw [free_add,ht]; rfl
  have hs1 : ordinalPartialSize (.one : OrdinalExpression (σ::Γ))=1 := rfl
  have he : inflated τ t=.add (repeatPos (copies τ-1) (.add t .one)) t := by
    unfold inflated repeatPos
    rw [← hk']
  rw [he,size_add_active _ _ (by rw [free_add,repeat_active _ hp]; rfl),repeat_size _ hp,
    size_add_active t .one hp,hs1]
  rw [← hk']
  unfold coefficient
  ring_nf
  omega
end LogicLineages.OrdinalComparison.Source.OneUnit.Proof
