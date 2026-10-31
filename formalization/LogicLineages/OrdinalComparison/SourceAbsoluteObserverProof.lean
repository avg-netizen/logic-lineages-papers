module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverProbeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
open AdmissibleAssignment ForwardTranslation
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

theorem two_ground {Γ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) :
    ∀ σ ∈ Ty.ground :: Ty.ground :: Γ, σ = Ty.ground := by
  intro σ hσ
  simp only [List.mem_cons] at hσ
  rcases hσ with rfl | rfl | hσ
  · rfl
  · rfl
  · exact hΓ σ hσ

theorem paired_probe_comparison {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (t : OriginalTerm Γ τ) (ρ : OrdinalComponent Γ → Nat)
    (v : OrdinalVector Γ τ.level) (hv : assignment OrdinalSyntax.defaultPolicy t = some v)
    (n : Nat) (hn : denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal))
    (x y : Nat) (p q : OrdinalVector (.ground :: .ground :: Γ) 0)
    (hp : assignment OrdinalSyntax.defaultPolicy (originalProbe t) = some p)
    (hq : assignment OrdinalSyntax.defaultPolicy (closedProbe hΓ t) = some q) :
    (denote (fun c => ((extend ρ x y c+1 : Nat) : Ordinal)) (p 0) =
      denote (fun c => ((extend ρ x y c+1 : Nat) : Ordinal)) (q 0)) ↔
      factor τ*n + (x+1) = factor τ*anchor hΓ t + (y+1) := by
  obtain ⟨w,s,hw,hsc,hcode,hclosed,hopen,hposC,hvalue⟩ := anchorCorrect Γ hΓ τ t
  let vv := SourceRenaming.renameVector (shiftTwo Γ) v
  let ww := SourceRenaming.renameVector (fromEmpty (.ground:: .ground::Γ)) w
  let ν : OrdinalComponent (.ground:: .ground::Γ) → Ordinal :=
    fun c => ((extend ρ x y c+1 : Nat) : Ordinal)
  have hvv : assignment OrdinalSyntax.defaultPolicy (t.rename (shiftTwo Γ)) = some vv := by
    rw [SourceRenaming.Proof.assignmentNaturality, hv]
    rfl
  have hww : assignment OrdinalSyntax.defaultPolicy ((close hΓ t).rename (fromEmpty _)) = some ww := by
    rw [SourceRenaming.Proof.assignmentNaturality, hw]
    rfl
  have hvvalue (j : Fin (τ.level+1)) :
      denote ν (vv j) = denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v j) := by
    rw [show vv j = ordinalExpressionRename (shiftTwo Γ) (v j) from rfl, rename_value]
    congr 1
    funext c
    rcases c with ⟨σ,z,i⟩
    cases σ <;> rfl
  have hwvalue (j : Fin (τ.level+1)) : denote ν (ww j) = denote (fun _ => 1) (w j) := by
    rw [show ww j = ordinalExpressionRename (fromEmpty _) (w j) from rfl, rename_value]
    congr 1
    funext c
    rcases c with ⟨σ,z,i⟩
    nomatch z
  have hn' : denote ν (vv 0) = (n : Ordinal) := (hvvalue 0).trans hn
  have hm' : denote ν (ww 0) = (anchor hΓ t : Ordinal) := (hwvalue 0).trans (hvalue _)
  have hclose := GroundClosing.Proof.assignmentNaturality Γ [] τ (closingMap hΓ)
    OrdinalSyntax.defaultPolicy t
  rw [hv] at hclose
  change assignment OrdinalSyntax.defaultPolicy (close hΓ t) =
    some (GroundClosing.vector (closingMap hΓ) v) at hclose
  have hwv := Option.some.inj (hw.symm.trans hclose)
  obtain ⟨vg,hvg,hg⟩ := actualAdmissibleAssignmentGenerated Γ τ OrdinalSyntax.defaultPolicy t
  have hevg := Option.some.inj (hvg.symm.trans hv)
  subst vg
  have hpositive : ∀ j, 0 < j.val → denote ν (vv j) = denote ν (ww j) := by
    intro j hj
    rw [hvvalue, hwvalue, hwv]
    change denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v j) =
      denote (fun _ => 1) (GroundClosing.expression (closingMap hΓ) (v j))
    rw [closing_value]
    exact closed_value (v j) (actualGeneratedGroundPositiveClosed Γ hΓ j.val (v j) hj (hg j)) _ _
  exact probe_comparison (two_ground hΓ) (t.rename (shiftTwo Γ))
    ((close hΓ t).rename (fromEmpty _)) .here (.there .here) (extend ρ x y)
    vv ww hvv hww n (anchor hΓ t) hn' hm' hpositive p q hp hq

theorem fullAbsoluteObserver : Targets.FullAbsoluteObserver := by
  refine ⟨open_evaluator_computable, closed_evaluator_computable, encodedScalarComputable, anchorCorrect, ?_⟩
  intro Γ hΓ τ t ρ z
  obtain ⟨v,n,hv,hn,hval⟩ := source_scalar hΓ t ρ
  have hfactor : 0 < factor τ := by unfold factor; omega
  constructor
  · rintro ⟨x,y,k,⟨p,hp,hpv⟩,⟨q,hq,hqv⟩,heq⟩
    have hpq := hpv.trans hqv.symm
    have he := (paired_probe_comparison hΓ t ρ v hv n hval x y p q hp hq).mp hpq
    have hm : factor τ*z = factor τ*n := by omega
    have hzn : z=n := Nat.eq_of_mul_eq_mul_left hfactor hm
    exact ⟨v,hv,by rw [hzn]; exact hval⟩
  · rintro ⟨w,hw,hwv⟩
    have he := Option.some.inj (hw.symm.trans hv)
    subst w
    have hnz : n=z := Nat.cast_injective (hval.symm.trans hwv)
    subst z
    let x := factor τ*anchor hΓ t
    let y := factor τ*n
    obtain ⟨p,np,hp,hnp,hpv⟩ := source_scalar (two_ground hΓ) (originalProbe t) (extend ρ x y)
    obtain ⟨q,nq,hq,hnq,hqv⟩ := source_scalar (two_ground hΓ) (closedProbe hΓ t) (extend ρ x y)
    have hlin : factor τ*n+(x+1) = factor τ*anchor hΓ t+(y+1) := by
      dsimp [x,y]
      omega
    have hpq := (paired_probe_comparison hΓ t ρ v hv n hval x y p q hp hq).mpr hlin
    have hs : np-1+1=np := by omega
    refine ⟨x,y,np-1,⟨p,hp,?_⟩,⟨q,hq,?_⟩,hlin⟩
    · rw [hs]
      exact hpv
    · rw [hs]
      exact hpq.symm.trans hpv
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
