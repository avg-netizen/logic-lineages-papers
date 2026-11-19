module
public import LogicLineages.ControlSensitivityCurrent.CurrentOneUnitPartialProof
public import LogicLineages.ControlSensitivityCurrent.GenericScalarProof
public import LogicLineages.OrdinalComparison.ParametricSourceSuccessorDenotationProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentOneUnit

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof
open AdmissibleAssignment ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)
open LogicLineages.PermittedControl.SelectedHardnessScalarSyntaxProof (repeated_value)

private theorem actualVectorGrade (p : AdmissibleSum.Policy) {Γ : List Ty} {τ : Ty}
    (a : OriginalTerm Γ τ) (u : OrdinalVector Γ τ.level) (ha : assignment p a = some u) :
    ∀ j, GeneratedOrdinalGrade Γ j.val (u j) := by
  obtain ⟨w,hw,hg⟩ := actualAdmissibleAssignmentGenerated Γ τ p a
  have same : w = u := Option.some.inj (hw.symm.trans ha)
  subst w
  exact hg

theorem commonUnitValuation {Γ : List Ty} (ρ : Variable Γ .ground → Nat) :
    (fun c => ((ExistentialPlan.inputs ρ c+1 : Nat) : Ordinal)) = commonUnits ρ := by
  funext c
  rcases c with ⟨τ,x,j⟩
  cases τ with
  | ground => rfl
  | arrow a b =>
    change ((1 : Nat) : Ordinal) = 1
    exact Nat.cast_one

private theorem selectedHeadClosure (f : Nat → Nat) {Γ : List Ty} {σ : Ty}
    (ρ : Variable Γ .ground → Nat) (e : OrdinalExpression (σ :: Γ)) :
    denoteWith f (commonUnits ρ) (ordinalHeadClosure e) =
      denoteWith f (fun c => ((headUnitWires ρ c+1 : Nat) : Ordinal)) e := by
  unfold ordinalHeadClosure
  rw [ParametricSourceSuccessor.Proof.exactSubstitution]
  congr 1
  funext c
  rcases c with ⟨τ,x,j⟩
  cases x with
  | here =>
    change (1 : Ordinal) = ((1 : Nat) : Ordinal)
    exact Nat.cast_one.symm
  | there x =>
    change commonUnits ρ ⟨τ,x,j⟩ = ((ExistentialPlan.inputs ρ ⟨τ,x,j⟩+1 : Nat) : Ordinal)
    exact (congrFun (commonUnitValuation ρ) ⟨τ,x,j⟩).symm

private theorem finiteAt (f : Nat → Nat) {Γ : List Ty} (ρ : OrdinalComponent Γ → Nat)
    (e : OrdinalExpression Γ) (hg : GeneratedOrdinalGrade Γ 0 e) :
    ∃ n : Nat, 0 < n ∧ denoteWith f (fun c => ((ρ c+1 : Nat) : Ordinal)) e = (n : Ordinal) := by
  obtain ⟨hpos,hfin⟩ := GenericScalar.generatedPositiveFinite f Γ ρ 0 e hg
  obtain ⟨n,hn⟩ := hfin rfl
  rw [hn] at hpos
  exact ⟨n,by exact_mod_cast hpos,hn⟩

private theorem collectActual {α : Type} (n : Nat) (f : Fin n → Option α) (v : Fin n → α)
    (hv : collect n f = some v) : ∀ i, f i = some (v i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨a,ha,w,hw,he⟩ : ∃ a, f 0 = some a ∧ ∃ w,
        collect n (fun i => f i.succ) = some w ∧ Fin.cases a w = v := by
      simpa only [collect,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using hv
    subst v
    exact Fin.cases ha (fun j => ih _ _ hw j)

private theorem abstractionScalar (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} {σ : Ty} {m : Nat} (h : OrdinalVector (σ :: Γ) m)
    (v : OrdinalPartialVector Γ σ) (l : OrdinalVector Γ (max (σ.level+1) m))
    (hv : AdmissiblePartial.run p 0 (h 0) = some v)
    (hl : abstraction p h = some l) (ρ : Variable Γ .ground → Nat) (P R : Nat)
    (hP : denoteWith f (commonUnits ρ) (v 0) = (P : Ordinal))
    (hR : denoteWith f (fun c => ((headUnitWires ρ c+1 : Nat) : Ordinal)) (h 0) = (R : Ordinal)) :
    denoteWith f (commonUnits ρ) (l 0) = ((OneUnit.multiplier h*P+R : Nat) : Ordinal) := by
  unfold abstraction at hl
  cases hc : collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) with
  | none => simp [hc] at hl
  | some q =>
    simp only [hc,bind,pure,Option.bind_some,Option.some.injEq] at hl
    have hq := collectActual _ _ q hc 0
    have hqv := Option.some.inj (hq.symm.trans hv)
    subst l
    change ordinalNaturalSum
      (denoteWith f (commonUnits ρ) (repeated p .scalarRepeat (OneUnit.multiplier h) (q 0 0)))
      (denoteWith f (commonUnits ρ) (ordinalHeadClosure (h 0))) = _
    rw [hqv,repeated_value f p (commonUnits ρ) _ P _ hP,selectedHeadClosure f ρ,hR,naturalSum_finite]

private theorem lambdaScalar (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} {σ τ : Ty} (a : OriginalTerm (σ :: Γ) τ)
    (h : OrdinalVector (σ :: Γ) τ.level) (ha : assignment p a = some h)
    (v : OrdinalPartialVector Γ σ) (hv : AdmissiblePartial.run p 0 (h 0) = some v)
    (ρ : Variable Γ .ground → Nat) (P R : Nat)
    (hP : denoteWith f (commonUnits ρ) (v 0) = (P : Ordinal))
    (hR : denoteWith f (fun c => ((headUnitWires ρ c+1 : Nat) : Ordinal)) (h 0) = (R : Ordinal)) :
    CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (.lam a) (OneUnit.multiplier h*P+R) := by
  obtain ⟨l,hl,_⟩ := actualAdmissibleAssignmentGenerated Γ (.arrow σ τ) p (.lam a)
  have hL := hl
  change (assignment p a).bind (abstraction p) = some l at hL
  rw [ha] at hL
  refine ⟨l,hl,?_⟩
  rw [commonUnitValuation ρ]
  exact abstractionScalar p f h v l hv hL ρ P R hP hR

private theorem freePartial (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} {σ : Ty} (ρ : Variable Γ .ground → Nat) (e : OrdinalExpression (σ :: Γ))
    (he : ordinalHeadFree e = true) (v : OrdinalPartialVector Γ σ)
    (hv : AdmissiblePartial.run p 0 e = some v) (R : Nat)
    (hR : denoteWith f (fun c => ((headUnitWires ρ c+1 : Nat) : Ordinal)) e = (R : Ordinal)) :
    denoteWith f (commonUnits ρ) (v 0) = ((R+1 : Nat) : Ordinal) := by
  rw [AdmissiblePartial.run.eq_def,he] at hv
  simp only [↓reduceIte,Option.some.injEq] at hv
  rw [← hv]
  change ordinalNaturalSum (denoteWith f (commonUnits ρ) (ordinalHeadClosure e)) 1 = _
  rw [selectedHeadClosure f ρ,hR]
  simpa only [Nat.cast_one] using naturalSum_finite R 1

private theorem inflatedValue (p : AdmissibleSum.Policy) (f : Nat → Nat)
    {Γ : List Ty} {τ : Ty} (ν : OrdinalComponent Γ → Ordinal)
    (e : OrdinalExpression Γ) (R : Nat) (hR : denoteWith f ν e = (R : Ordinal)) :
    denoteWith f ν (inflated p τ e) =
      ((OneUnit.coefficient τ*R+OneUnit.copies τ : Nat) : Ordinal) := by
  have he : denoteWith f ν (.add e .one) = ((R+1 : Nat) : Ordinal) := by
    simpa only [denoteWith,hR,Nat.cast_one] using naturalSum_finite R 1
  change ordinalNaturalSum (denoteWith f ν (repeated p .scalarRepeat (OneUnit.copies τ) (.add e .one)))
    (denoteWith f ν e) = _
  rw [repeated_value f p ν (OneUnit.copies τ) (R+1) _ he,hR,naturalSum_finite]
  congr 1
  unfold OneUnit.coefficient
  ring

theorem actualScalarRows : CurrentOneUnitTargets.ActualScalarRows := by
  intro p f Γ σ τ a d hd
  obtain ⟨h,h',d₀,ha,hu,hd₀,hdata,hposdi,hInfl,hsize⟩ := literalInflation p Γ σ τ a
  have hdataD : d = (OneUnit.multiplier h,OneUnit.multiplier h',ordinalHeadFree (h 0)) :=
    (Option.some.inj (hd.symm.trans hd₀)).trans hdata
  have gh := actualVectorGrade p a h ha
  have gh' := actualVectorGrade p (OneUnit.unused a) h' hu
  obtain ⟨v,hv,gv⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ σ p 0 (h 0) (gh 0)
  obtain ⟨v',hv',gv'⟩ := AdmissiblePartial.actualAdmissiblePartialGenerated Γ σ p 0 (h' 0) (gh' 0)
  refine ⟨h,h',v,v',ha,hu,hv,hv',?_⟩
  intro ρ
  obtain ⟨P,hp,hP⟩ := finiteAt f (ExistentialPlan.inputs ρ) (v 0) (gv 0)
  obtain ⟨P',hp',hP'⟩ := finiteAt f (ExistentialPlan.inputs ρ) (v' 0) (gv' 0)
  rw [commonUnitValuation ρ] at hP hP'
  obtain ⟨R,hr,hR⟩ := finiteAt f (headUnitWires ρ) (h 0) (gh 0)
  obtain ⟨R',hr',hR'⟩ := finiteAt f (headUnitWires ρ) (h' 0) (gh' 0)
  let L := d.1*P+R
  let L' := d.2.1*P'+R'
  have hL : CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (OneUnit.first a) L := by
    unfold L
    rw [hdataD]
    exact lambdaScalar p f a h ha v hv ρ P R hP hR
  have hL' : CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (OneUnit.second a) L' := by
    unfold L'
    rw [hdataD]
    exact lambdaScalar p f (OneUnit.unused a) h' hu v' hv' ρ P' R' hP' hR'
  refine ⟨P,R,P',R',L,L',hp,hr,hp',hr',by dsimp [L]; omega,by dsimp [L']; omega,
    hP,hP',⟨h,ha,hR⟩,⟨h',hu,hR'⟩,hL,hL',rfl,rfl,?_,?_⟩
  · intro hfree
    have hfree' : ordinalHeadFree (h 0) = true := by rw [hdataD] at hfree; exact hfree
    have he := hP.symm.trans (freePartial p f ρ (h 0) hfree' v hv R hR)
    have he' : P = R+1 := by exact_mod_cast he
    refine ⟨he',?_⟩
    dsimp [L]
    rw [he']
    ring
  · intro hactive
    have hactive' : ordinalHeadFree (h 0) = false := by rw [hdataD] at hactive; exact hactive
    obtain ⟨w,hw,he⟩ := inflatedPartialValue (τ:=τ) p f (commonUnits ρ) (h 0) hactive' v P hv hP
    have eW : w = v' := by
      rw [hInfl] at hv'
      exact Option.some.inj (hw.symm.trans hv')
    subst w
    have hP'' : P' = OneUnit.coefficient τ*P+4*OneUnit.copies τ := by
      exact_mod_cast hP'.symm.trans he
    have hx := inflatedValue (τ:=τ) p f (fun c => ((headUnitWires ρ c+1 : Nat) : Ordinal)) (h 0) R hR
    have hR'' : R' = OneUnit.coefficient τ*R+OneUnit.copies τ := by
      rw [hInfl] at hR'
      exact_mod_cast hR'.symm.trans hx
    refine ⟨hP'',hR'',?_⟩
    dsimp [L']
    rw [hP'',hR'']
    ring

end LogicLineages.ControlSensitivityCurrent.CurrentOneUnit
