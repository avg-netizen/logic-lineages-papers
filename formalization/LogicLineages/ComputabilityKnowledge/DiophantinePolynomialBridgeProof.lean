module

public import LogicLineages.ComputabilityKnowledge.Comparators.DiophantinePolynomialBridge
public import LogicLineages.ComputabilityKnowledge.PolynomialCircuitProof
public import Mathlib.Algebra.MvPolynomial.Variables

@[expose] public section

/-! External Codex continuation supplier bridge. Witness finiteness is derived
from actual polynomial support even when Mathlib's auxiliary type is arbitrary.
All witness/code selections here are existential, not algorithms on proofs. -/
namespace LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridgeProof

open PolynomialCircuit DiophantinePolynomialBridge

private theorem isPoly_eval {α γ : Type} (P : MvPolynomial α Int)
    (v : α → (γ → Nat) → Int) (hv : ∀ i, IsPoly (v i)) :
    IsPoly (fun ν => MvPolynomial.eval (fun i => v i ν) P) := by
  induction P using MvPolynomial.induction_on with
  | C z => simpa using (IsPoly.const z : IsPoly (fun _ : γ → Nat => z))
  | add P Q hP hQ =>
    have h := hP.sub ((IsPoly.const 0).sub hQ)
    simpa only [map_add,zero_sub,sub_neg_eq_add] using h
  | mul_X P i hP => simpa using hP.mul (hv i)

theorem polynomialCorrespondence : Comparators.DiophantinePolynomialBridge.PolynomialCorrespondence := by
  intro α f
  constructor
  · intro hf
    induction hf with
    | proj i => exact ⟨MvPolynomial.X i,fun _ => by simp⟩
    | const z => exact ⟨MvPolynomial.C z,fun _ => by simp⟩
    | sub hf hg ihf ihg =>
      obtain ⟨P,hP⟩ := ihf
      obtain ⟨Q,hQ⟩ := ihg
      exact ⟨P-Q,fun ν => by simp [hP,hQ]⟩
    | mul hf hg ihf ihg =>
      obtain ⟨P,hP⟩ := ihf
      obtain ⟨Q,hQ⟩ := ihg
      exact ⟨P*Q,fun ν => by simp [hP,hQ]⟩
  · rintro ⟨P,hP⟩
    have h := isPoly_eval P (fun i ν => (ν i : Int)) (fun i => IsPoly.proj i)
    have he : (fun ν => MvPolynomial.eval (fun i => (ν i : Int)) P) = f := funext hP
    exact he ▸ h

private theorem finite_support_witnesses {n : Nat} {β : Type}
    (p : Poly (Fin n ⊕ β)) :
    ∃ (m : Nat) (Q : MvPolynomial (Fin n ⊕ Fin m) Int),
      ∀ ν, (∃ t : β → Nat, p (Sum.elim ν t) = 0) ↔
        ∃ w : Fin m → Nat, MvPolynomial.eval (fun i => ((Sum.elim ν w i : Nat) : Int)) Q = 0 := by
  classical
  obtain ⟨P,hP⟩ := (polynomialCorrespondence _ p).mp p.isPoly
  let s : Finset β := P.vars.biUnion (fun i => match i with | .inl _ => ∅ | .inr b => {b})
  let e : s ≃ Fin (Fintype.card s) := Fintype.equivFin s
  let j : Fin (Fintype.card s) → β := fun k => (e.symm k).val
  let f : Fin n ⊕ Fin (Fintype.card s) → Fin n ⊕ β := Sum.map id j
  have hj : Function.Injective j := by
    intro a b h
    apply e.symm.injective
    exact Subtype.ext h
  have hf : Function.Injective f := by
    intro a b h
    cases a <;> cases b <;> simp only [f,Sum.map_inl,Sum.map_inr,id_eq] at h
    · exact congrArg Sum.inl (Sum.inl.inj h)
    · cases h
    · cases h
    · exact congrArg Sum.inr (hj (Sum.inr.inj h))
  have hs (b : β) (hb : Sum.inr b ∈ P.vars) : b ∈ s := by
    apply Finset.mem_biUnion.mpr
    exact ⟨Sum.inr b,hb,by simp⟩
  have hvars : (P.vars : Set (Fin n ⊕ β)) ⊆ Set.range f := by
    intro i hi
    cases i with
    | inl a => exact ⟨Sum.inl a,rfl⟩
    | inr b =>
      refine ⟨Sum.inr (e ⟨b,hs b hi⟩),?_⟩
      simp [f,j]
  obtain ⟨Q,hQ⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range P f hf hvars
  have heval (ν : Fin n → Nat) (t : β → Nat) :
      MvPolynomial.eval (fun i => ((Sum.elim ν (t ∘ j) i : Nat) : Int)) Q = p (Sum.elim ν t) := by
    rw [←hP,←hQ,MvPolynomial.eval_rename]
    apply congrArg (fun v : Fin n ⊕ Fin (Fintype.card s) → Int => MvPolynomial.eval v Q)
    funext i
    cases i <;> rfl
  refine ⟨Fintype.card s,Q,?_⟩
  intro ν
  constructor
  · rintro ⟨t,ht⟩
    exact ⟨t ∘ j,(heval ν t).trans ht⟩
  · rintro ⟨w,hw⟩
    let t : β → Nat := fun b => if h : b ∈ s then w (e ⟨b,h⟩) else 0
    have ht : t ∘ j = w := by
      funext k
      simp [t,j,Function.comp_def]
    refine ⟨t,?_⟩
    rw [←heval ν t,ht]
    exact hw

theorem finiteWitnessExtraction : Comparators.DiophantinePolynomialBridge.FiniteWitnessExtraction := by
  intro n S
  constructor
  · rintro ⟨β,p,hp⟩
    obtain ⟨m,Q,hQ⟩ := finite_support_witnesses p
    exact ⟨m,Q,fun ν => (hp ν).trans (hQ ν)⟩
  · rintro ⟨m,Q,hQ⟩
    have hpoly := (polynomialCorrespondence (Fin n ⊕ Fin m)
      (fun ν => MvPolynomial.eval (fun i => (ν i : Int)) Q)).mpr ⟨Q,fun _ => rfl⟩
    exact ⟨Fin m,⟨_,hpoly⟩,hQ⟩

theorem framingFaithful : Comparators.DiophantinePolynomialBridge.FramingFaithful := by
  intro n m ν w
  refine ⟨?_,?_,?_,?_⟩
  · intro i
    simp [joinedNat,i.isLt]
  · intro j
    have hn : ¬n+j.val<n := by omega
    simp [joinedNat,hn,j.isLt]
  · intro a b h
    cases a with
    | inl a => cases b with
      | inl b => exact congrArg Sum.inl (Fin.ext h)
      | inr b => simp only [sumIndex,Sum.elim_inl,Sum.elim_inr] at h; omega
    | inr a => cases b with
      | inl b => simp only [sumIndex,Sum.elim_inl,Sum.elim_inr] at h; omega
      | inr b =>
        apply congrArg Sum.inr
        apply Fin.ext
        simpa [sumIndex] using h
  · intro i
    cases i with
    | inl i => simp only [sumIndex,Sum.elim_inl]; omega
    | inr i => simp only [sumIndex,Sum.elim_inr]; omega

private theorem joined_sumIndex (n m : Nat) (ν : Fin n → Nat) (w : Fin m → Nat)
    (i : Fin n ⊕ Fin m) : joinedNat ν w (sumIndex n m i) = Sum.elim ν w i := by
  cases i with
  | inl i => exact (framingFaithful n m ν w).1 i
  | inr i => exact (framingFaithful n m ν w).2.1 i

theorem codeCoverage : Comparators.DiophantinePolynomialBridge.CodeCoverage := by
  intro n m P
  let g : Fin n ⊕ Fin m → Fin (n+m) := fun i =>
    ⟨sumIndex n m i,(framingFaithful n m (fun _ => 0) (fun _ => 0)).2.2.2 i⟩
  obtain ⟨p,hpn,hpw,hp⟩ := PolynomialCircuitProof.coverage (n+m) (MvPolynomial.rename g P)
  have he : interpret p = MvPolynomial.rename (sumIndex n m) P := by
    rw [hp,MvPolynomial.rename_rename]
    rfl
  refine ⟨p,hpn,hpw,he,?_⟩
  intro ν w
  rw [he,MvPolynomial.eval_rename]
  apply congrArg (fun v : Fin n ⊕ Fin m → Int => MvPolynomial.eval v P)
  funext i
  exact congrArg (fun x : Nat => (x : Int)) (joined_sumIndex n m ν w i)

private theorem joined_polynomial (n m : Nat) (P : MvPolynomial Nat Int) :
    IsPoly (fun u : Fin n ⊕ Fin m → Nat =>
      MvPolynomial.eval (fun i => (joinedNat (fun a => u (.inl a)) (fun b => u (.inr b)) i : Int)) P) := by
  apply isPoly_eval
  intro i
  by_cases hi : i < n
  · simpa [joinedNat,hi] using (IsPoly.proj (Sum.inl (⟨i,hi⟩ : Fin n)) :
      IsPoly (fun u : Fin n ⊕ Fin m → Nat => (u (.inl ⟨i,hi⟩) : Int)))
  · by_cases hj : i-n < m
    · simpa [joinedNat,hi,hj] using (IsPoly.proj (Sum.inr (⟨i-n,hj⟩ : Fin m)) :
        IsPoly (fun u : Fin n ⊕ Fin m → Nat => (u (.inr ⟨i-n,hj⟩) : Int)))
    · simpa [joinedNat,hi,hj] using (IsPoly.const 0 : IsPoly (fun _ : Fin n ⊕ Fin m → Nat => 0))

theorem diophantineCodeRepresentation : Comparators.DiophantinePolynomialBridge.DiophantineCodeRepresentation := by
  intro n S
  constructor
  · intro hS
    obtain ⟨m,P,hP⟩ := (finiteWitnessExtraction n S).mp hS
    obtain ⟨p,hpn,hpw,he,heval⟩ := codeCoverage n m P
    refine ⟨m,p,hpn,hpw,?_⟩
    intro ν
    rw [hP ν]
    exact exists_congr (fun w => by rw [heval])
  · rintro ⟨m,p,hpn,hpw,hp⟩
    refine ⟨Fin m,⟨_,joined_polynomial n m (interpret p)⟩,?_⟩
    intro ν
    exact hp ν

private theorem power_diophantine : Dioph powerGraph := by
  have hp : Dioph.DiophFn (fun ν : Fin 2 → Nat => ν 0 ^ ν 1) :=
    Dioph.pow_dioph (Dioph.proj_dioph 0) (Dioph.proj_dioph 1)
  let index : Option (Fin 2) → Fin 3 := fun i => match i with
    | none => 2
    | some j => ⟨j.val,by omega⟩
  have h := Dioph.reindex_dioph (Fin 3) index hp
  exact Dioph.ext h (fun ν => Iff.rfl)

theorem powerGraphRepresentation : Comparators.DiophantinePolynomialBridge.PowerGraphRepresentation :=
  (diophantineCodeRepresentation 3 powerGraph).mp power_diophantine

theorem diophantinePolynomialBridge : Comparators.DiophantinePolynomialBridge.Target :=
  ⟨polynomialCorrespondence,finiteWitnessExtraction,framingFaithful,codeCoverage,
    diophantineCodeRepresentation,powerGraphRepresentation⟩

end LogicLineages.ComputabilityKnowledge.DiophantinePolynomialBridgeProof
