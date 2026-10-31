module
public import LogicLineages.OrdinalComparison.SourceOneUnitLiteralProof
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverUnusedProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Proof
open AdmissibleAssignment
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

def inflatedPartial {Γ σ} (τ : Ty) (p : OrdinalPartialVector Γ σ) : OrdinalPartialVector Γ σ :=
  addPartial (repeatPartial (copies τ-1) (addPartial p (ordinalFreePartialVector 0 .one))) p

theorem run_inflated {Γ σ} (τ : Ty) (t : OrdinalExpression (σ :: Γ))
    (ht : ordinalHeadFree t=false) (p : OrdinalPartialVector Γ σ)
    (hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 t=some p) :
    AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (inflated τ t)=some (inflatedPartial τ p) := by
  have hk : copies τ=(copies τ-1)+1 := by unfold copies; omega
  have ha : ordinalHeadFree (.add t .one)=false := by rw [free_add,ht]; rfl
  have hap := run_add t .one ht p (ordinalFreePartialVector 0 .one) hp rfl
  have he : inflated τ t=.add (repeatPos (copies τ-1) (.add t .one)) t := by
    unfold inflated repeatPos
    rw [← hk]
  rw [he]
  exact run_add _ _ (repeat_active _ ha _) _ _ (run_repeat _ ha _ hap _) hp

theorem addPartial_value {Γ σ} (ν : OrdinalComponent Γ → Ordinal)
    (p q : OrdinalPartialVector Γ σ) (P Q : Nat)
    (hp : denote ν (p 0)=(P : Ordinal)) (hq : denote ν (q 0)=(Q : Ordinal)) :
    denote ν (addPartial p q 0)=((P+Q+1 : Nat) : Ordinal) := by
  change ordinalNaturalSum (ordinalNaturalSum (denote ν (p 0)) (denote ν (q 0))) 1 = _
  rw [hp,hq,naturalSum_finite]
  simpa only [Nat.cast_one] using naturalSum_finite (P+Q) 1

theorem one_partial_value {Γ σ} (ν : OrdinalComponent Γ → Ordinal) :
    denote ν (ordinalFreePartialVector (σ := σ) 0 .one 0)=(2 : Ordinal) := by
  change ordinalNaturalSum 1 1 = (2 : Ordinal)
  simpa using naturalSum_finite 1 1

theorem repeatPartial_value {Γ σ} (ν : OrdinalComponent Γ → Ordinal)
    (p : OrdinalPartialVector Γ σ) (P : Nat) (hp : denote ν (p 0)=(P : Ordinal)) (n : Nat) :
    denote ν (repeatPartial n p 0)=(((n+1)*P+n : Nat) : Ordinal) := by
  induction n with
  | zero => simpa only [repeatPartial,Nat.zero_add,Nat.one_mul,Nat.add_zero] using hp
  | succ n ih =>
    change denote ν (addPartial (repeatPartial n p) p 0) = _
    rw [addPartial_value ν _ _ _ _ ih hp]
    congr 1
    ring

theorem inflatedPartial_value {Γ σ} (ν : OrdinalComponent Γ → Ordinal) (τ : Ty)
    (p : OrdinalPartialVector Γ σ) (P : Nat) (hp : denote ν (p 0)=(P : Ordinal)) :
    denote ν (inflatedPartial τ p 0)=((coefficient τ*P+4*copies τ : Nat) : Ordinal) := by
  have hplus := addPartial_value ν p (ordinalFreePartialVector 0 .one) P 2 hp (one_partial_value ν)
  have hrep := repeatPartial_value ν _ _ hplus (copies τ-1)
  have hv := addPartial_value ν _ p _ P hrep hp
  change denote ν (inflatedPartial τ p 0)=_ at hv
  rw [hv]
  congr 1
  have hk : copies τ=(copies τ-1)+1 := by unfold copies; omega
  rw [← hk]
  unfold coefficient
  ring_nf
  omega

theorem active_partial_value {Γ σ} (ν : OrdinalComponent Γ → Ordinal) (τ : Ty)
    (t : OrdinalExpression (σ::Γ)) (ht : ordinalHeadFree t=false)
    (p q : OrdinalPartialVector Γ σ)
    (hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 t=some p)
    (hq : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (inflated τ t)=some q)
    (P : Nat) (hP : denote ν (p 0)=(P : Ordinal)) :
    denote ν (q 0)=((coefficient τ*P+4*copies τ : Nat) : Ordinal) := by
  have he := Option.some.inj (hq.symm.trans (run_inflated τ t ht p hp))
  rw [he]
  exact inflatedPartial_value ν τ p P hP
end LogicLineages.OrdinalComparison.Source.OneUnit.Proof
