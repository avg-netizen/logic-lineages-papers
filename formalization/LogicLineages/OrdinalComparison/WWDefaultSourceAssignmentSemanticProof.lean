module
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxBoxStatementChecks
public import LogicLineages.OrdinalComparison.WWDefaultSyntaxAbstractionStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.Proof
open SyntaxCode OrdinalSyntax
private theorem typed_check {Γ τ} (t : OriginalTerm Γ τ) :
    check (Γ.map typeCode) (encodeTerm t) = some (typeCode τ) :=
  (SyntaxCode.StatementChecks.typedCheckExact Γ τ _).mpr ⟨t,rfl⟩
private theorem level_exact (τ : Ty) : typeLevel (typeCode τ) = τ.level :=
  SyntaxCode.StatementChecks.typeLevelExact τ
private theorem range_map {α : Type} (n : Nat) (f : Nat → α) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro j hj hk; simp
private theorem tag (p k : Nat) (hk : k<8) : (8*p+k)%8=k := by omega
private theorem payload (p k : Nat) (hk : k<8) : (8*p+k)/8=p := by omega

theorem assignmentCorrect : Targets.AssignmentCorrect := by
  intro Γ τ t
  induction t with
  | var v =>
    rw [assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, primeCode, AdmissibleAssignment.assignment,
      level_exact, range_map, vectorCode, typedCode,
      OrdinalSyntax.code, componentCode]
  | zeroC =>
    rw [assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, primeCode, AdmissibleAssignment.assignment,
      level_exact, vectorCode, typedCode, OrdinalSyntax.code]
    rfl
  | succC =>
    rw [assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, primeCode, AdmissibleAssignment.assignment,
      level_exact, vectorCode, typedCode, OrdinalSyntax.code]
    rfl
  | caseC σ =>
    rw [assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, tag _ 3 (by decide), payload _ 3 (by decide),
      primeCode, AdmissibleAssignment.assignment, level_exact,
      vectorCode, typedCode, OrdinalSyntax.code]
    rfl
  | recC σ =>
    rw [assignmentCode, typed_check]
    simp only [encodeTerm, erase, SyntaxCode.code, tag _ 4 (by decide), payload _ 4 (by decide),
      Option.bind_some, show 4<5 from by decide, ↓reduceDIte, primeCode, show ¬(4=0) from by decide,
      show 4=4 from rfl, ↓reduceIte, level_exact,
      AdmissibleAssignment.assignment, Option.map_some]
    apply congrArg some
    rw [range_map]
    change List.ofFn _ = List.ofFn _
    apply List.ext_getElem
    · simp [level_exact]
    · intro i hi hk
      simp only [List.getElem_ofFn]
      split_ifs <;> simp [typedCode, OrdinalSyntax.code, AdmissibleAssignment.numeral,
        AdmissibleAssignment.repeated, defaultPolicy, defaultShape, leftShape,
        AdmissibleSum.expand, repeatCode, sumPrefix, node]
  | @app Γ σ τ f a ihf iha =>
    rw [assignmentCode, typed_check]
    simp only [encodeTerm, erase, SyntaxCode.code, tag _ 5 (by decide), payload _ 5 (by decide),
      Nat.unpair_pair, Option.bind_some, show ¬(5<5) from by decide, ↓reduceDIte,
      show 5=5 from rfl, true_or, ↓reduceIte]
    change (do
      let aty ← check (Γ.map typeCode) (encodeTerm a)
      let vf ← assignmentCode (Γ.map typeCode) (encodeTerm f)
      let va ← assignmentCode (Γ.map typeCode) (encodeTerm a)
      pure (defaultApplicationCode (typeLevel (typeCode τ)) (typeLevel aty) vf va)) = _
    rw [typed_check, ihf, iha]
    cases hf : AdmissibleAssignment.assignment defaultPolicy f <;>
      cases ha : AdmissibleAssignment.assignment defaultPolicy a <;>
      simp [AdmissibleAssignment.assignment, hf, ha, level_exact,
        defaultSyntaxApplicationCorrect]
    exact defaultSyntaxApplicationCorrect Γ σ τ _ _
  | @lam Γ σ τ b ih =>
    rw [assignmentCode, typed_check]
    simp only [encodeTerm, erase, SyntaxCode.code, tag _ 6 (by decide), payload _ 6 (by decide),
      Nat.unpair_pair, Option.bind_some, show ¬(6<5) from by decide, ↓reduceDIte,
      show ¬(6=5) from by decide, show 6=6 from rfl, or_true, ↓reduceIte]
    change (do
      let bt ← check ((σ::Γ).map typeCode) (encodeTerm b)
      let vb ← assignmentCode ((σ::Γ).map typeCode) (encodeTerm b)
      abstractionCode (typeLevel (typeCode σ)) (typeLevel bt) vb) = _
    rw [typed_check, ih]
    cases hb : AdmissibleAssignment.assignment defaultPolicy b <;>
      simp [AdmissibleAssignment.assignment, hb, level_exact,
        defaultSyntaxAbstractionCorrect]
    · rfl
    · exact defaultSyntaxAbstractionCorrect Γ σ τ.level _
  | ranked s _ _ => nomatch s

theorem assignmentChecked : Targets.AssignmentChecked := by
  intro Γ n v h
  rw [assignmentCode] at h
  cases hc : check Γ n with
  | none => simp [hc] at h
  | some τ => exact ⟨τ,rfl⟩

theorem assignmentSourceExact : Targets.AssignmentSourceExact := by
  intro Γ n v
  constructor
  · intro h
    obtain ⟨k,hk⟩ := assignmentChecked _ _ _ h
    have ht : check (Γ.map typeCode) n = some (typeCode (decodeType k)) := by
      rw [SyntaxCode.StatementChecks.typeEncodeDecode]; exact hk
    obtain ⟨t,he⟩ := (SyntaxCode.StatementChecks.typedCheckExact Γ (decodeType k) n).mp ht
    rw [←he,assignmentCorrect] at h
    obtain ⟨w,hw,hv⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_,t,w,he,hw,hv⟩
  · rintro ⟨τ,t,w,he,hw,hv⟩
    rw [←he,assignmentCorrect,hw,Option.map_some,hv]
end LogicLineages.OrdinalComparison.Source.DefaultSourceAssignment.Proof
