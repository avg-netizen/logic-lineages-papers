module
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.PackageDecisionProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.SourceMetadataProof
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.NumericProgramsProof
public import LogicLineages.OrdinalComparison.LevelTwoCounterexample.SourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.DecisionProof
open Source Source.ForwardTranslation Source.SourceClasses LevelTwoCounterexample

/-- The literal numeric checker sees the same original all-ground context. -/
theorem ground_context_codes (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) :
    Γ.map SyntaxCode.typeCode = List.replicate Γ.length 0 := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
      have he := hΓ σ List.mem_cons_self
      have hr : ∀ τ ∈ Γ, τ = Ty.ground :=
        fun τ hτ => hΓ τ (List.mem_cons_of_mem σ hτ)
      simp only [List.map_cons,List.length_cons,List.replicate_succ,he,SyntaxCode.typeCode,ih hr]

theorem typed_accepts (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ)
    (hla : InternalLevelBound 2 a) (hlb : InternalLevelBound 2 b) (mode : Nat) :
    Admission.accepts (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b) = true := by
  have ha := (AdmissionProof.actualInternalBound Γ τ a 2).mpr hla
  have hb := (AdmissionProof.actualInternalBound Γ υ b 2).mpr hlb
  rw [ground_context_codes Γ hΓ] at ha hb
  simp only [Admission.accepts,ha,hb,Bool.and_true]

/-- Reuse the accepted comparison equivalence for these very original typed
terms and their canonical assignments, then decide its emitted counterexample. -/
theorem actualTypedDecision : Targets.ActualTypedDecision := by
  classical
  intro Γ hΓ τ υ a b hla hlb mode
  obtain ⟨av,bv,p,hav,hbv,hcompile,hrelation⟩ :=
    SourceProof.actualLevelTwoCounterexamples Γ hΓ τ υ a b hla hlb mode
  let q : SourceCode.Input := (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)
  have haccept : Admission.accepts q = true := typed_accepts Γ hΓ τ υ a b hla hlb mode
  have hp : Admission.compile q = some p := by
    rw [(AdmissionProof.exactGuardedDomain q).2.2 haccept]
    exact hcompile
  have hcert := MetadataProof.emittedPackageMetadata q p hp
  have hpackage := actualPackageDecision p hcert
  obtain ⟨hdecision,hsolve⟩ := decision_of_package q p hp
  refine ⟨av,bv,hav,hbv,?_,?_⟩
  · change decision q = some (solve q)
    rw [hdecision,hsolve]
  · change solve q = true ↔ _
    rw [hsolve]
    constructor
    · intro hs ρ hρ
      by_contra hbad
      have hclosed := hrelation.mpr ⟨ρ,hρ,hbad⟩
      have htrue := hpackage.mpr hclosed
      simp only [htrue,Bool.not_true,Bool.false_eq_true] at hs
    · intro hall
      cases hbool : packageCounterexample p with
      | false => rfl
      | true =>
          obtain ⟨ρ,hρ,hbad⟩ := hrelation.mp (hpackage.mp hbool)
          exact False.elim (hbad (hall ρ hρ))

/-- A concrete uniform numerical witness, with no caller-supplied classifier,
package metadata, word solver, or termination premise. -/
theorem fullInternalLevelTwoComparison : Targets.FullInternalLevelTwoComparison := by
  refine ⟨solve,ProgramsProof.solve_computable,?_⟩
  intro Γ hΓ τ υ a b hla hlb mode
  obtain ⟨av,bv,hav,hbv,_,hdecision⟩ := actualTypedDecision Γ hΓ τ υ a b hla hlb mode
  exact ⟨av,bv,hav,hbv,hdecision⟩

#print axioms ground_context_codes
#print axioms typed_accepts
#print axioms actualTypedDecision
#print axioms fullInternalLevelTwoComparison

end LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.DecisionProof
