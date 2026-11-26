module
public import LogicLineages.PermittedControl.SelectedSourceDomainTargets
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainProof

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSourceDomainProof
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

 theorem headDomain : SelectedSourceDomainTargets.HeadDomain := by
  intro f Γ σ i t ht
  induction ht with
  | one i => exact .free i _ rfl
  | omega i hi => exact .free i _ rfl
  | var x j =>
    cases x with
    | here => exact .tracked j
    | there v => exact .free _ _ rfl
  | add ha hb iha ihb => exact .add iha ihb
  | emul hi ha hb iha ihb => exact .emul hi iha ihb
  | collapse ha hb hg iha ihb => exact .collapse iha ihb
  | promote hi ht hf ih => exact .free _ _ hf

 theorem head_high_free (f : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (i : Nat) (t : OrdinalExpression (σ::Γ)) (ht : HeadGrade f Γ σ i t)
    (hi : σ.level < i) : ordinalHeadFree t = true := by
  induction ht with
  | one i => rfl
  | omega i _ => rfl
  | var x j =>
    cases x with
    | here => have := j.isLt; omega
    | there v => rfl
  | add ha hb iha ihb =>
    have hf := iha hi
    have hg := ihb hi
    simp only [ordinalHeadFree, ordinalHeadOccurs, Bool.not_or] at *
    simp only [hf,hg,Bool.true_and]
  | emul hpos ha hb iha ihb =>
    have hf := iha (by omega)
    have hg := ihb hi
    simp only [ordinalHeadFree, ordinalHeadOccurs, Bool.not_or] at *
    simp only [hf,hg,Bool.true_and]
  | collapse ha hb hg iha ihb => omega
  | promote hpos ht hf ih => exact hf

 theorem free_closure_reconstruct {Γ : List Ty} {σ : Ty}
    (t : OrdinalExpression (σ::Γ)) (ht : ordinalHeadFree t = true) :
    LiteralCovariance.weaken σ (ordinalHeadClosure t) = t := by
  induction t with
  | var c =>
    rcases c with ⟨τ,x,j⟩
    cases x with
    | here => simp [ordinalHeadFree,ordinalHeadOccurs,ordinalHeadComponentOccurs] at ht
    | there v => rfl
  | zero | one | omega => rfl
  | add a b ha hb | emul a b ha hb | collapse a b ha hb =>
    have hs : ordinalHeadFree a = true ∧ ordinalHeadFree b = true := by
      simpa only [ordinalHeadFree,ordinalHeadOccurs,Bool.not_or,Bool.and_eq_true] using ht
    have ha' := ha hs.1
    have hb' := hb hs.2
    simp only [LiteralCovariance.weaken,ordinalExpressionRename,ordinalHeadClosure,substitute] at *
    rw [ha',hb']

 theorem highCoordinateFree : SelectedSourceDomainTargets.HighCoordinateFree := by
  intro f Γ σ i t ht hi
  have hf := head_high_free f Γ σ i t ht hi
  exact ⟨hf,free_closure_reconstruct t hf⟩

 theorem uniquePartial : SelectedSourceDomainTargets.UniquePartial := by
  intro f Γ σ p i t ht
  exact LiteralPartialDomain.actualLiteralPartialUniqueBound Γ σ p i t
    (headDomain f Γ σ i t ht)

 theorem collect_success {α : Type} (n : Nat) (g : Fin n → Option α)
    (hg : ∀ i, ∃ v, g i = some v) : ∃ v, AdmissibleAssignment.collect n g = some v := by
  induction n with
  | zero => exact ⟨Fin.elim0,rfl⟩
  | succ n ih =>
    obtain ⟨a,ha⟩ := hg 0
    obtain ⟨v,hv⟩ := ih (fun i => g i.succ) (fun i => hg i.succ)
    exact ⟨Fin.cases a v,by simp [AdmissibleAssignment.collect,ha,hv]⟩

 theorem option_unique {α : Type} (x : Option α) (hx : ∃ a, x = some a) :
    ∃! a, x = some a := by
  obtain ⟨a,ha⟩ := hx
  exact ⟨a,ha,fun b hb => Option.some.inj (hb.symm.trans ha)⟩

 theorem vector_collect_success (f : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (p : Policy) (m : Nat) (h : OrdinalVector (σ::Γ) m)
    (hh : ∀ i, HeadGrade f Γ σ i.val (h i)) :
    ∃ ps, AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) = some ps := by
  apply collect_success
  intro i
  obtain ⟨v,hv,_⟩ := uniquePartial f Γ σ p i.val (h i) (hh i)
  exact ⟨v,hv.1⟩

 theorem uniqueVectorOperations : SelectedSourceDomainTargets.UniqueVectorOperations := by
  intro f Γ σ p m h hh
  have hc := vector_collect_success f Γ σ p m h hh
  refine ⟨option_unique _ hc,?_,?_⟩
  · apply option_unique
    obtain ⟨ps,hps⟩ := hc
    unfold LiteralCovariance.delta
    rw [hps]
    exact ⟨_,rfl⟩
  · apply option_unique
    obtain ⟨ps,hps⟩ := hc
    unfold AdmissibleAssignment.abstraction
    rw [hps]
    exact ⟨_,rfl⟩

 theorem deltaHighRetention : SelectedSourceDomainTargets.DeltaHighRetention := by
  intro f Γ σ p m h hh v hv j hj hm
  obtain ⟨ps,hps⟩ := vector_collect_success f Γ σ p m h hh
  unfold LiteralCovariance.delta at hv
  rw [hps] at hv
  have hv' := Option.some.inj hv
  have he := congrFun hv' j
  have hj0 : j.val ≠ 0 := by omega
  have hjn : ¬j.val < σ.level+2 := by omega
  simp only [hj0,hjn,↓reduceIte,↓reduceDIte] at he
  rw [← he]
  exact (highCoordinateFree f Γ σ j.val (h ⟨j.val,hm⟩) (hh _) (by omega)).2

 theorem fullSelectedSourceDomain : SelectedSourceDomainTargets.FullSelectedSourceDomain :=
  ⟨headDomain,highCoordinateFree,uniquePartial,uniqueVectorOperations,deltaHighRetention⟩

end LogicLineages.PermittedControl.SelectedSourceDomainProof
