module
public import LogicLineages.StandardControlCurrent.PolicyAssignmentTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckStatementChecks
public import LogicLineages.StandardControlCurrent.PolicyConstructorsSyntaxProof
public import LogicLineages.StandardControlCurrent.PolicyAbstractionSyntaxProof
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentStatementChecks
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyAssignmentSyntaxProof
open OrdinalComparison Source Source.SyntaxCode Source.OrdinalSyntax
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

theorem literal : PolicyAssignmentTargets.LiteralCalibration := by
  intro p Γ τ t
  induction t with
  | var v =>
    rw [PolicyAssignment.assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, PolicyAssignment.primeCode, AdmissibleAssignment.assignment,
      level_exact, range_map, vectorCode, typedCode,
      OrdinalSyntax.code, componentCode]
  | zeroC =>
    rw [PolicyAssignment.assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, PolicyAssignment.primeCode, AdmissibleAssignment.assignment,
      level_exact, vectorCode, typedCode, OrdinalSyntax.code]
    try rfl
  | succC =>
    rw [PolicyAssignment.assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, PolicyAssignment.primeCode, AdmissibleAssignment.assignment,
      level_exact, vectorCode, typedCode, OrdinalSyntax.code]
    try rfl
  | caseC σ =>
    rw [PolicyAssignment.assignmentCode, typed_check]
    simp [encodeTerm, erase, SyntaxCode.code, tag _ 3 (by decide), payload _ 3 (by decide),
      PolicyAssignment.primeCode, AdmissibleAssignment.assignment, level_exact,
      vectorCode, typedCode, OrdinalSyntax.code]
    try rfl
  | recC σ =>
    rw [PolicyAssignment.assignmentCode, typed_check]
    simp only [encodeTerm,erase,SyntaxCode.code,tag _ 4 (by decide),payload _ 4 (by decide),
      Option.bind_some,bind,pure,show 4<5 from by decide,if_true,PolicyAssignment.primeCode,
      show ¬(4=0) from by decide,if_false,level_exact]
    exact PolicyConstructorsSyntaxProof.constants.2.2.2 p Γ σ
  | @app Γ σ τ f a ihf iha =>
    rw [PolicyAssignment.assignmentCode, typed_check]
    simp only [encodeTerm, erase, SyntaxCode.code, tag _ 5 (by decide), payload _ 5 (by decide),
      Nat.unpair_pair, Option.bind_some, show ¬(5<5) from by decide, ↓reduceDIte,
      show 5=5 from rfl, true_or, ↓reduceIte]
    change (do
      let aty ← check (Γ.map typeCode) (encodeTerm a)
      let vf ← PolicyAssignment.assignmentCode p (Γ.map typeCode) (encodeTerm f)
      let va ← PolicyAssignment.assignmentCode p (Γ.map typeCode) (encodeTerm a)
      PolicyConstructors.applicationCode p (typeLevel (typeCode τ)) (typeLevel aty) vf va) = _
    rw [typed_check, ihf, iha]
    cases hf : AdmissibleAssignment.assignment p f <;>
      cases ha : AdmissibleAssignment.assignment p a <;>
      simp [AdmissibleAssignment.assignment, hf, ha, level_exact,
        PolicyConstructorsSyntaxProof.application p]
    exact PolicyConstructorsSyntaxProof.application p Γ σ τ _ _
  | @lam Γ σ τ b ih =>
    rw [PolicyAssignment.assignmentCode, typed_check]
    simp only [encodeTerm, erase, SyntaxCode.code, tag _ 6 (by decide), payload _ 6 (by decide),
      Nat.unpair_pair, Option.bind_some, show ¬(6<5) from by decide, ↓reduceDIte,
      show ¬(6=5) from by decide, show 6=6 from rfl, or_true, ↓reduceIte]
    change (do
      let bt ← check ((σ::Γ).map typeCode) (encodeTerm b)
      let vb ← PolicyAssignment.assignmentCode p ((σ::Γ).map typeCode) (encodeTerm b)
      PolicyAbstraction.abstractionCode p (typeLevel (typeCode σ)) (typeLevel bt) vb) = _
    rw [typed_check, ih]
    cases hb : AdmissibleAssignment.assignment p b <;>
      simp [AdmissibleAssignment.assignment, hb, level_exact,
        PolicyAbstractionSyntaxProof.literal p]
    · rfl
    · exact PolicyAbstractionSyntaxProof.literal p Γ σ τ.level _
  | ranked s _ _ => nomatch s

theorem checked (p : AdmissibleSum.Policy) : ∀ Γ n v, PolicyAssignment.assignmentCode p Γ n=some v → ∃ τ, check Γ n=some τ := by
  intro Γ n v h
  rw [PolicyAssignment.assignmentCode] at h
  cases hc : check Γ n with
  | none => simp [hc] at h
  | some τ => exact ⟨τ,rfl⟩

theorem sourceExact : PolicyAssignmentTargets.SourceExact := by
  intro p Γ n v
  constructor
  · intro h
    obtain ⟨k,hk⟩ := checked p _ _ _ h
    have ht : check (Γ.map typeCode) n = some (typeCode (decodeType k)) := by
      rw [SyntaxCode.StatementChecks.typeEncodeDecode]; exact hk
    obtain ⟨t,he⟩ := (SyntaxCode.StatementChecks.typedCheckExact Γ (decodeType k) n).mp ht
    rw [←he,literal] at h
    obtain ⟨w,hw,hv⟩ := Option.map_eq_some_iff.mp h
    exact ⟨_,t,w,he,hw,hv⟩
  · rintro ⟨τ,t,w,he,hw,hv⟩
    rw [←he,literal,hw,Option.map_some,hv]

theorem success : PolicyAssignmentTargets.TypedSuccess := by
  intro p Γ τ t
  obtain ⟨w,hw,hg⟩ := OrdinalComparison.StatementChecks.fixed_actualAdmissibleAssignmentGenerated Γ τ p t
  refine ⟨w,hw,?_,hg⟩
  rw [literal,hw,Option.map_some]
end LogicLineages.StandardControlCurrent.PolicyAssignmentSyntaxProof
