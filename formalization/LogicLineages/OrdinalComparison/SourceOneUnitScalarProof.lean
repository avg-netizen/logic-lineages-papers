module
public import LogicLineages.OrdinalComparison.SourceOneUnitTargets
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverUnusedProof
public import LogicLineages.OrdinalComparison.WWOriginalAssignmentNormProof
public import LogicLineages.OrdinalComparison.WWOriginalWeakPartialProof
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OneUnit.Proof
open AdmissibleAssignment OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

theorem scalar_nat {Γ} (t : OrdinalExpression Γ) (ht : AmbientGrade Γ 0 t)
    (ρ : AdmissibleSubstitution Γ) : ∃ n : Nat, 0<n ∧ expressionValue ρ t=(n : Ordinal) := by
  obtain ⟨n,hn⟩ := originalAmbientScalarFinite Γ t ht ρ
  have hp := originalAmbientGradePositive Γ 0 t ht ρ
  rw [hn] at hp
  exact ⟨n,by exact_mod_cast hp,hn⟩

theorem source_bundle {Γ τ} (a : OriginalTerm Γ τ) :
    ∃ h : OrdinalVector Γ τ.level,
      assignment OrdinalSyntax.defaultPolicy a=some h ∧
      (∀ j, AmbientGrade Γ j.val (h j)) ∧ (∀ j, GeneratedOrdinalGrade Γ j.val (h j)) := by
  obtain ⟨h,hh,hg,hb⟩ := originalSourceAssignmentBounded Γ τ OrdinalSyntax.defaultPolicy a
  obtain ⟨v,hv,vg⟩ := actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy a
  have he := Option.some.inj (hv.symm.trans hh)
  subst v
  exact ⟨h,hh,hg,vg⟩

theorem head_partial {Γ σ m} (h : OrdinalVector (σ::Γ) m)
    (ha : ∀ j, AmbientGrade (σ::Γ) j.val (h j))
    (hg : ∀ j, GeneratedOrdinalGrade (σ::Γ) j.val (h j)) :
    ∃ ps : OrdinalPartialVector Γ σ,
      AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (h 0)=some ps ∧
      ∀ j, AmbientGrade Γ j.val (ps j) := by
  have hh := originalGeneratedAmbientHead Γ σ 0 (h 0) (hg 0) (ha 0)
  obtain ⟨ps,hps,hpg,hw⟩ := originalPartialWeakAndValid Γ σ OrdinalSyntax.defaultPolicy 0 (h 0) hh
  exact ⟨ps,hps,hpg⟩

theorem collect_success {α : Type} (n : Nat) (f : Fin n → Option α) (v : Fin n → α)
    (hv : collect n f=some v) : ∀ i, f i=some (v i) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
    obtain ⟨a,ha,w,hw,he⟩ : ∃ a,f 0=some a ∧ ∃ w,
        collect n (fun i => f i.succ)=some w ∧ Fin.cases a w=v := by
      simpa only [collect,bind,pure,Option.bind_eq_some_iff,Option.some.injEq] using hv
    subst v
    intro i
    exact Fin.cases ha (fun j => ih _ _ hw j) i

theorem closure_value {Γ σ} (ρ : AdmissibleSubstitution Γ) (t : OrdinalExpression (σ::Γ)) :
    expressionValue ρ (ordinalHeadClosure t)=expressionValue (unitExtension (σ := σ) ρ) t :=
  originalHeadClosureValue Γ σ ρ (unitExtension ρ) (fun _ => rfl) (fun _ _ => rfl) t

theorem abstraction_scalar {Γ σ m} (h : OrdinalVector (σ::Γ) m)
    (ps : OrdinalPartialVector Γ σ) (l : OrdinalVector Γ (max (σ.level+1) m))
    (hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 (h 0)=some ps)
    (hl : abstraction OrdinalSyntax.defaultPolicy h=some l)
    (ρ : AdmissibleSubstitution Γ) (P R : Nat)
    (hP : expressionValue ρ (ps 0)=(P : Ordinal))
    (hR : expressionValue (unitExtension (σ := σ) ρ) (h 0)=(R : Ordinal)) :
    expressionValue ρ (l 0)=((multiplier h*P+R : Nat) : Ordinal) := by
  unfold abstraction at hl
  cases hc : collect (m+1) (fun i => AdmissiblePartial.run OrdinalSyntax.defaultPolicy i.val (h i)) with
  | none => simp [hc] at hl
  | some q =>
    simp only [hc,bind,pure,Option.bind_some,Option.some.injEq] at hl
    have hq := collect_success _ _ q hc 0
    have hq0 := Option.some.inj (hq.symm.trans hp)
    subst l
    change ordinalNaturalSum
      (denote (valuation ρ) (repeated OrdinalSyntax.defaultPolicy .scalarRepeat (multiplier h) (q 0 0)))
      (expressionValue ρ (ordinalHeadClosure (h 0))) = _
    rw [hq0,AbsoluteObserver.Proof.repeated_value (valuation ρ) _ P _ hP,closure_value,hR,naturalSum_finite]

theorem lambda_value {Γ σ τ} (a : OriginalTerm (σ::Γ) τ)
    (h : OrdinalVector (σ::Γ) τ.level) (l : OrdinalVector Γ (Ty.arrow σ τ).level)
    (ha : assignment OrdinalSyntax.defaultPolicy a=some h)
    (hl : assignment OrdinalSyntax.defaultPolicy (.lam a)=some l) :
    abstraction OrdinalSyntax.defaultPolicy h=some l := by
  change (assignment OrdinalSyntax.defaultPolicy a).bind (abstraction OrdinalSyntax.defaultPolicy)=some l at hl
  rw [ha] at hl
  exact hl

theorem free_partial_value {Γ σ} (ρ : AdmissibleSubstitution Γ)
    (t : OrdinalExpression (σ::Γ)) (ht : ordinalHeadFree t=true) (ps : OrdinalPartialVector Γ σ)
    (hp : AdmissiblePartial.run OrdinalSyntax.defaultPolicy 0 t=some ps)
    (R : Nat) (hR : expressionValue (unitExtension (σ := σ) ρ) t=(R : Ordinal)) :
    expressionValue ρ (ps 0)=((R+1 : Nat) : Ordinal) := by
  rw [AdmissiblePartial.run.eq_def,ht] at hp
  simp only [↓reduceIte,Option.some.injEq] at hp
  rw [← hp]
  change ordinalNaturalSum (expressionValue ρ (ordinalHeadClosure t)) 1 = _
  rw [closure_value,hR]
  simpa only [Nat.cast_one] using naturalSum_finite R 1
end LogicLineages.OrdinalComparison.Source.OneUnit.Proof
