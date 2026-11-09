module
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionTargets
import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceProof
import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckProof
import LogicLineages.OrdinalComparison.SourceTypesProofs

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionProof
open Source Source.SyntaxCode Source.SourceClasses Source.SourceTypeSupport

private theorem subtype_level (τ σ : Ty) (h : σ ∈ τ.subtypes) : σ.level ≤ τ.level := by
  induction τ with
  | ground =>
    have hs : σ = Ty.ground := by simpa [Ty.subtypes] using h
    subst σ
    exact le_rfl
  | arrow a b iha ihb =>
    simp only [Ty.subtypes, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact le_rfl
    · exact (iha h).trans ((Nat.le_succ _).trans (Nat.le_max_left _ _))
    · exact (ihb h).trans (Nat.le_max_right _ _)

private theorem bound_subtypes (τ : Ty) (L : Nat) :
    (∀ σ ∈ τ.subtypes.toFinset, σ.level ≤ L) ↔ τ.level ≤ L := by
  constructor
  · intro h
    exact h τ (List.mem_toFinset.mpr (Ty.mem_subtypes_self τ))
  · intro h σ hs
    exact (subtype_level τ σ (List.mem_toFinset.mp hs)).trans h

private theorem bound_union (s t : Finset Ty) (L : Nat) :
    (∀ σ ∈ s ∪ t, σ.level ≤ L) ↔
      (∀ σ ∈ s, σ.level ≤ L) ∧ (∀ σ ∈ t, σ.level ≤ L) := by
  simp only [Finset.mem_union, or_imp, forall_and]

private theorem bound_leaf {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ)
    (ht : typeSupport t = τ.subtypes.toFinset) (L : Nat) :
    InternalLevelBound L t ↔ τ.level ≤ L := by
  unfold InternalLevelBound
  rw [ht]
  exact bound_subtypes τ L

private theorem bound_app {Γ : List Ty} {σ τ : Ty}
    (f : OriginalTerm Γ (.arrow σ τ)) (a : OriginalTerm Γ σ) (L : Nat) :
    InternalLevelBound L (.app f a) ↔
      τ.level ≤ L ∧ InternalLevelBound L f ∧ InternalLevelBound L a := by
  change (∀ υ ∈ τ.subtypes.toFinset ∪ (typeSupport f ∪ typeSupport a), υ.level ≤ L) ↔ _
  simp only [bound_union, bound_subtypes, InternalLevelBound]

private theorem bound_lam {Γ : List Ty} {σ τ : Ty}
    (b : OriginalTerm (σ :: Γ) τ) (L : Nat) :
    InternalLevelBound L (.lam b) ↔
      (Ty.arrow σ τ).level ≤ L ∧ InternalLevelBound L b := by
  change (∀ υ ∈ (Ty.arrow σ τ).subtypes.toFinset ∪ typeSupport b, υ.level ≤ L) ↔ _
  simp only [bound_union, bound_subtypes, InternalLevelBound]

private theorem typed_check {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) :
    check (Γ.map typeCode) (encodeTerm t) = some (typeCode τ) :=
  (Source.SyntaxCode.Proof.typedCheckExact Γ τ (encodeTerm t)).mpr ⟨t, rfl⟩

private theorem mod_tag (a tag : Nat) (h : tag < 8) : (8 * a + tag) % 8 = tag := by
  omega

private theorem div_tag (a tag : Nat) (h : tag < 8) : (8 * a + tag) / 8 = a := by
  omega

private theorem test_leaf {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) (L : Nat)
    (h5 : encodeTerm t % 8 ≠ 5) (h6 : encodeTerm t % 8 ≠ 6) :
    Admission.test L (Γ.map typeCode) (encodeTerm t) = decide (τ.level ≤ L) := by
  rw [Admission.test]
  simp [typed_check, Source.SyntaxCode.Proof.typeLevelExact τ, h5, h6]

private theorem test_app {Γ : List Ty} {σ τ : Ty}
    (f : OriginalTerm Γ (.arrow σ τ)) (a : OriginalTerm Γ σ) (L : Nat) :
    Admission.test L (Γ.map typeCode) (encodeTerm (.app f a)) =
      (decide (τ.level ≤ L) &&
        (Admission.test L (Γ.map typeCode) (encodeTerm f) &&
         Admission.test L (Γ.map typeCode) (encodeTerm a))) := by
  rw [Admission.test]
  simp only [typed_check, Option.any_some, Source.SyntaxCode.Proof.typeLevelExact τ]
  simp [encodeTerm, erase, code, mod_tag _ 5 (by decide),
    div_tag _ 5 (by decide), Nat.unpair_pair]

private theorem test_lam {Γ : List Ty} {σ τ : Ty}
    (b : OriginalTerm (σ :: Γ) τ) (L : Nat) :
    Admission.test L (Γ.map typeCode) (encodeTerm (.lam b)) =
      (decide ((Ty.arrow σ τ).level ≤ L) &&
        Admission.test L ((σ :: Γ).map typeCode) (encodeTerm b)) := by
  rw [Admission.test]
  simp only [typed_check, Option.any_some, Source.SyntaxCode.Proof.typeLevelExact (.arrow σ τ)]
  simp [encodeTerm, erase, code, mod_tag _ 6 (by decide),
    div_tag _ 6 (by decide), Nat.unpair_pair]

/-- Each actual node is checked in its original local context. Literal
subtypes of its result type have no greater level; the existing support
recursion supplies precisely the application children and lambda body. -/
theorem actualInternalBound : AdmissionTargets.ActualInternalBound := by
  intro Γ τ t L
  induction t with
  | var v =>
    rw [test_leaf (.var v) L (by simp [encodeTerm, erase, code])
      (by simp [encodeTerm, erase, code]),
      bound_leaf (.var v) (by simp [typeSupport]) L]
    simp only [decide_eq_true_eq]
  | zeroC =>
    rw [test_leaf .zeroC L (by simp [encodeTerm, erase, code])
      (by simp [encodeTerm, erase, code]),
      bound_leaf .zeroC (by simp [typeSupport]) L]
    simp only [decide_eq_true_eq]
  | succC =>
    rw [test_leaf .succC L (by simp [encodeTerm, erase, code])
      (by simp [encodeTerm, erase, code]),
      bound_leaf .succC (by simp [typeSupport]) L]
    simp only [decide_eq_true_eq]
  | caseC σ =>
    rw [test_leaf (.caseC σ) L
      (by simp [encodeTerm, erase, code, mod_tag _ 3 (by decide)])
      (by simp [encodeTerm, erase, code, mod_tag _ 3 (by decide)]),
      bound_leaf (.caseC σ) (by simp [typeSupport]) L]
    simp only [decide_eq_true_eq]
  | recC σ =>
    rw [test_leaf (.recC σ) L
      (by simp [encodeTerm, erase, code, mod_tag _ 4 (by decide)])
      (by simp [encodeTerm, erase, code, mod_tag _ 4 (by decide)]),
      bound_leaf (.recC σ) (by simp [typeSupport]) L]
    simp only [decide_eq_true_eq]
  | app f a ihf iha =>
    rw [test_app, bound_app]
    simp only [Bool.and_eq_true, decide_eq_true_eq, ihf, iha]
  | lam b ih =>
    rw [test_lam, bound_lam]
    simp only [Bool.and_eq_true, decide_eq_true_eq, ih]
  | ranked s _ _ => cases s

theorem exactTypedAdmission : AdmissionTargets.ExactTypedAdmission := by
  intro Γ τ L n
  simp only [Admission.typedAccepts, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨ht, hc⟩
    obtain ⟨t, he⟩ := (Source.SyntaxCode.Proof.typedCheckExact Γ τ n).mp hc
    refine ⟨t, he, ?_⟩
    apply (actualInternalBound Γ τ t L).mp
    simpa only [he] using ht
  · rintro ⟨t, rfl, hb⟩
    exact ⟨(actualInternalBound Γ τ t L).mpr hb, typed_check t⟩

theorem malformedRejection : AdmissionTargets.MalformedRejection := by
  intro L Γ n h
  rw [Admission.test]
  simp [h]

theorem exactAnyTypeAdmission : AdmissionTargets.ExactAnyTypeAdmission := by
  intro Γ L n
  constructor
  · intro ht
    cases hc : check (Γ.map typeCode) n with
    | none =>
      have hf := malformedRejection L (Γ.map typeCode) n hc
      simp only [hf, Bool.false_eq_true] at ht
    | some c =>
      have htyped : check (Γ.map typeCode) n = some (typeCode (decodeType c)) := by
        simpa only [Source.SyntaxCode.Proof.typeEncodeDecode c] using hc
      obtain ⟨t, he⟩ :=
        (Source.SyntaxCode.Proof.typedCheckExact Γ (decodeType c) n).mp htyped
      refine ⟨decodeType c, t, he, ?_⟩
      apply (actualInternalBound Γ (decodeType c) t L).mp
      simpa only [he] using ht
  · rintro ⟨τ, t, rfl, hb⟩
    exact (actualInternalBound Γ τ t L).mpr hb

private theorem ground_test (k n : Nat) :
    Admission.test 2 (List.replicate k 0) n = true ↔
      ∃ (τ : Ty) (t : OriginalTerm (List.replicate k Ty.ground) τ),
        encodeTerm t = n ∧ InternalLevelBound 2 t := by
  simpa only [List.map_replicate, typeCode] using
    exactAnyTypeAdmission (List.replicate k Ty.ground) 2 n

theorem exactGroundClass : AdmissionTargets.ExactGroundClass := by
  intro p
  simp only [Admission.accepts, Bool.and_eq_true, ground_test]
  constructor
  · rintro ⟨⟨τ, a, ha, hla⟩, ⟨υ, b, hb, hlb⟩⟩
    exact ⟨τ, υ, a, b, ha, hb, hla, hlb⟩
  · rintro ⟨τ, υ, a, b, ha, hb, hla, hlb⟩
    exact ⟨⟨τ, a, ha, hla⟩, ⟨υ, b, hb, hlb⟩⟩

private theorem accepted_compile (q : SourceCode.Input)
    (h : Admission.accepts q = true) : ∃ p, SourceCode.compile q = some p := by
  obtain ⟨τ, υ, a, b, ha, hb, hla, hlb⟩ := (exactGroundClass q).mp h
  obtain ⟨av, bv, p, _, _, hp, _⟩ :=
    SourceProof.actualLevelTwoCounterexamples (List.replicate q.1 Ty.ground)
      (fun _ hs => List.eq_of_mem_replicate hs) τ υ a b hla hlb q.2.1
  refine ⟨p, ?_⟩
  simpa only [List.length_replicate, ha, hb] using hp

theorem exactGuardedDomain : AdmissionTargets.ExactGuardedDomain := by
  intro q
  cases h : Admission.accepts q with
  | false => simp [Admission.compile, h]
  | true =>
    obtain ⟨p, hp⟩ := accepted_compile q h
    simp [Admission.compile, h, hp]

theorem emittedSourceCounterexample : AdmissionTargets.EmittedSourceCounterexample := by
  intro q p hp
  have h : Admission.accepts q = true := by
    cases hq : Admission.accepts q with
    | false => simp [Admission.compile, hq] at hp
    | true => rfl
  obtain ⟨τ, υ, a, b, ha, hb, hla, hlb⟩ := (exactGroundClass q).mp h
  obtain ⟨av, bv, p', hav, hbv, hp', hrel⟩ :=
    SourceProof.actualLevelTwoCounterexamples (List.replicate q.1 Ty.ground)
      (fun _ hs => List.eq_of_mem_replicate hs) τ υ a b hla hlb q.2.1
  have hc' : SourceCode.compile q = some p' := by
    simpa only [List.length_replicate, ha, hb] using hp'
  have hc : SourceCode.compile q = some p := by
    simpa only [Admission.compile, h, if_true] using hp
  have he : p' = p := Option.some.inj (hc'.symm.trans hc)
  subst p'
  exact ⟨τ, υ, a, b, av, bv, ha, hb, hla, hlb, hav, hbv, hrel⟩

end LogicLineages.OrdinalComparison.LevelTwoCounterexample.AdmissionProof
