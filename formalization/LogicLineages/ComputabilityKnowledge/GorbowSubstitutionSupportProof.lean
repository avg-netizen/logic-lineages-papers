module

public import LogicLineages.ComputabilityKnowledge.Comparators.GorbowSubstitutionSupport
public import LogicLineages.ComputabilityKnowledge.GorbowFreeSupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupportProof
open GorbowSyntax GorbowFreeSupport GorbowFormulaSubstitution GorbowSubstitutionSupport

theorem termUses : Comparators.GorbowSubstitutionSupport.TermUses := by
  intro m n σ t j
  induction t <;> simp_all [GorbowSubstitution.substitute,Term.uses,Bool.or_eq_true,or_and_right,exists_or]
private theorem termUse {m n : Nat} (σ : Fin m → Term n) (t : Term m) (j : Fin n) :
    (GorbowSubstitution.substitute σ t).uses j=true ↔ ∃ i, t.uses i=true ∧ (σ i).uses j=true :=
  termUses m n σ t j

theorem renameUses : Comparators.GorbowSubstitutionSupport.RenameUses := by
  intro m n r t j
  change (GorbowSubstitution.substitute (fun i => Term.var (r i)) t).uses j=true ↔ _
  rw [termUse]
  constructor
  · rintro ⟨i,hi,hj⟩
    change decide (j=r i)=true at hj
    exact ⟨i,hi,(of_decide_eq_true hj).symm⟩
  · rintro ⟨i,hi,hj⟩
    exact ⟨i,hi,by change decide (j=r i)=true; simp [hj]⟩

theorem liftUses : Comparators.GorbowSubstitutionSupport.LiftUses := by
  intro m n σ
  constructor
  · intro i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [liftSubstitute,Term.uses]
    · have h := renameUses n (n+1) Fin.succ (σ k) 0
      simpa [liftSubstitute,Fin.succ_ne_zero] using h
  · intro i j
    refine Fin.cases ?_ (fun k => ?_) i
    · constructor
      · intro h
        change decide (j.succ=0)=true at h
        exact False.elim (Fin.succ_ne_zero j (of_decide_eq_true h))
      · rintro ⟨k,hk,_⟩
        exact False.elim (Fin.succ_ne_zero k hk.symm)
    · change (renameTerm Fin.succ (σ k)).uses j.succ=true ↔ _
      rw [renameUses n (n+1) Fin.succ (σ k) j.succ]
      constructor
      · rintro ⟨i,hi,he⟩
        have hij : i=j := Fin.succ_inj.mp he
        subst i
        exact ⟨k,rfl,hi⟩
      · rintro ⟨i,he,hi⟩
        have hki : k=i := Fin.succ_inj.mp he
        subst i
        exact ⟨j,hi,rfl⟩

private theorem liftedExists {m n : Nat} (σ : Fin m → Term n) (φ : Formula (m+1)) (j : Fin n) :
    (∃ i : Fin (m+1), φ.uses i=true ∧ (liftSubstitute σ i).uses j.succ=true) ↔
    ∃ k : Fin m, φ.uses k.succ=true ∧ (σ k).uses j=true := by
  constructor
  · rintro ⟨i,hi,hl⟩
    obtain ⟨k,rfl,hk⟩ := ((liftUses m n σ).2 i j).mp hl
    exact ⟨k,hi,hk⟩
  · rintro ⟨k,hk,hs⟩
    exact ⟨k.succ,hk,((liftUses m n σ).2 k.succ j).mpr ⟨k,rfl,hs⟩⟩

theorem formulaUses : Comparators.GorbowSubstitutionSupport.FormulaUses := by
  intro m n σ φ
  induction φ generalizing n with
  | equal a b => intro j; simp [substituteFormula,Formula.uses,termUse,or_and_right,exists_or]
  | universalRelation t => intro j; exact termUse σ t j
  | agent t => intro j; exact termUse σ t j
  | knowledgeAll t => intro j; exact termUse σ t j
  | knowledge a b => intro j; simp [substituteFormula,Formula.uses,termUse,or_and_right,exists_or]
  | truth t => intro j; exact termUse σ t j
  | neg φ ih => intro j; exact ih n σ j
  | imp a b iha ihb => intro j; simp [substituteFormula,Formula.uses,iha,ihb,or_and_right,exists_or]
  | conj a b iha ihb => intro j; simp [substituteFormula,Formula.uses,iha,ihb,or_and_right,exists_or]
  | disj a b iha ihb => intro j; simp [substituteFormula,Formula.uses,iha,ihb,or_and_right,exists_or]
  | all φ ih =>
    intro j
    exact (ih (n+1) (liftSubstitute σ) j.succ).trans (liftedExists σ φ j)
  | ex φ ih =>
    intro j
    exact (ih (n+1) (liftSubstitute σ) j.succ).trans (liftedExists σ φ j)

private theorem imageMember {m n : Nat} (σ : Fin m → Term n) (s : Finset Nat) (j : Nat) :
    j ∈ supportImage σ s ↔ ∃ i : Fin m, i.val ∈ s ∧ j ∈ termSupport (σ i) := by
  simp only [supportImage,Finset.mem_biUnion,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,hi⟩
    by_cases hs : i.val ∈ s
    · exact ⟨i,hs,by simpa [hs] using hi⟩
    · simp [hs] at hi
  · rintro ⟨i,hs,hi⟩
    exact ⟨i,by simpa [hs] using hi⟩

theorem exactSupports : Comparators.GorbowSubstitutionSupport.ExactSupports := by
  intro m n σ
  constructor
  · intro t
    ext j
    rw [imageMember]
    by_cases hj : j<n
    · let k : Fin n := ⟨j,hj⟩
      have ho := GorbowFreeSupportProof.usesCalibration.1 n (GorbowSubstitution.substitute σ t) k
      change j ∈ termSupport (GorbowSubstitution.substitute σ t) ↔ _ at ho
      rw [ho,termUse]
      constructor
      · rintro ⟨i,hi,hs⟩
        exact ⟨i,(GorbowFreeSupportProof.usesCalibration.1 m t i).mpr hi,
          (GorbowFreeSupportProof.usesCalibration.1 n (σ i) k).mpr hs⟩
      · rintro ⟨i,hi,hs⟩
        exact ⟨i,(GorbowFreeSupportProof.usesCalibration.1 m t i).mp hi,
          (GorbowFreeSupportProof.usesCalibration.1 n (σ i) k).mp hs⟩
    · constructor
      · intro h
        exact False.elim (hj (GorbowFreeSupportProof.supportBound.1 n _ j h))
      · rintro ⟨i,_,hi⟩
        exact False.elim (hj (GorbowFreeSupportProof.supportBound.1 n (σ i) j hi))
  · intro φ
    ext j
    rw [imageMember]
    by_cases hj : j<n
    · let k : Fin n := ⟨j,hj⟩
      have ho := GorbowFreeSupportProof.usesCalibration.2 n (substituteFormula σ φ) k
      change j ∈ formulaSupport (substituteFormula σ φ) ↔ _ at ho
      rw [ho,formulaUses m n σ φ k]
      constructor
      · rintro ⟨i,hi,hs⟩
        exact ⟨i,(GorbowFreeSupportProof.usesCalibration.2 m φ i).mpr hi,
          (GorbowFreeSupportProof.usesCalibration.1 n (σ i) k).mpr hs⟩
      · rintro ⟨i,hi,hs⟩
        exact ⟨i,(GorbowFreeSupportProof.usesCalibration.2 m φ i).mp hi,
          (GorbowFreeSupportProof.usesCalibration.1 n (σ i) k).mp hs⟩
    · constructor
      · intro h
        exact False.elim (hj (GorbowFreeSupportProof.supportBound.2 n _ j h))
      · rintro ⟨i,_,hi⟩
        exact False.elim (hj (GorbowFreeSupportProof.supportBound.1 n (σ i) j hi))

theorem gorbowSubstitutionSupport : Comparators.GorbowSubstitutionSupport.Target :=
  ⟨termUses,renameUses,liftUses,formulaUses,exactSupports⟩
end LogicLineages.ComputabilityKnowledge.GorbowSubstitutionSupportProof
