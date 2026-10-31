module
public import LogicLineages.OrdinalComparison.SourceAbsoluteObserverNumericProof
public import LogicLineages.OrdinalComparison.WWGroundClosingProof
public import LogicLineages.OrdinalComparison.WWCompiledVectorProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxVectorCompilerProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
open ForwardTranslation LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleAssignment

theorem closing_component {Γ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) (c : OrdinalComponent Γ) :
    GroundClosing.component (closingMap hΓ) c = .one := by
  rcases c with ⟨σ, x, j⟩
  cases groundType hΓ x
  rfl

theorem closing_value {Γ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (t : OrdinalExpression Γ) (ν : OrdinalComponent [] → Ordinal) :
    denote ν (GroundClosing.expression (closingMap hΓ) t) = denote (fun _ => 1) t := by
  induction t with
  | var c => simpa only [GroundClosing.expression, substitute, closing_component, denote]
  | zero | one | omega => rfl
  | add a b iha ihb | emul a b iha ihb | collapse a b iha ihb =>
    simp only [GroundClosing.expression, substitute, denote] at *
    rw [iha, ihb]

theorem scalar_of_vector {Γ n} (v : OrdinalVector Γ n)
    (c : CompiledVector (OrdinalComponent Γ) n) (hc : compileVector v = some c) :
    compileScalar (v 0) = some c.scalar := by
  obtain ⟨s, hs, p, hp, he⟩ : ∃ s, compileScalar (v 0) = some s ∧
      ∃ p, collect n (fun j => extractPositive (v j.succ)) = some p ∧
        CompiledVector.mk s p = c := by
    simpa only [compileVector, bind, pure, Option.bind_eq_some_iff, Option.some.injEq] using hc
  subst c
  exact hs

theorem ground_codes (Γ : List Ty) (hΓ : ∀ σ ∈ Γ, σ = Ty.ground) :
    Γ.map SyntaxCode.typeCode = List.replicate Γ.length (SyntaxCode.typeCode Ty.ground) := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    have hσ := hΓ σ List.mem_cons_self
    subst σ
    simp only [List.map_cons, List.length_cons, List.replicate_succ]
    rw [ih (fun τ hτ => hΓ τ (List.mem_cons_of_mem _ hτ))]

theorem numeric_evaluator_exact {Γ τ} (t : OriginalTerm Γ τ)
    (v : OrdinalVector Γ τ.level) (c : CompiledVector (OrdinalComponent Γ) τ.level)
    (hv : assignment OrdinalSyntax.defaultPolicy t = some v) (hc : compileVector v = some c) :
    (((DefaultSourceAssignment.assignmentCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t)).bind
        OrdinalSyntax.compileVectorCode).map (fun q => scalarSyntaxValue q.1 [])).getD 0 =
      c.scalar.value (fun _ => 1) := by
  rw [DefaultSourceAssignment.Proof.assignmentCorrect Γ τ t, hv]
  simp only [Option.map_some, Option.bind_some]
  rw [OrdinalSyntax.ordinalSyntaxVectorCompilerCorrect Γ τ.level v, hc]
  simp only [Option.map_some, Option.getD_some, CompiledVector.syntaxCode]
  rw [scalarSyntaxValueSourceCorrect]
  rfl

theorem source_scalar {Γ τ} (hΓ : ∀ σ ∈ Γ, σ = Ty.ground)
    (t : OriginalTerm Γ τ) (ρ : OrdinalComponent Γ → Nat) :
    ∃ v : OrdinalVector Γ τ.level, ∃ n : Nat,
      assignment OrdinalSyntax.defaultPolicy t = some v ∧ 0 < n ∧
      denote (fun c => ((ρ c+1 : Nat) : Ordinal)) (v 0) = (n : Ordinal) := by
  obtain ⟨v, hv, c, hc, hs⟩ := actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy t
  refine ⟨v, c.scalar.value (fun x => ρ x+1), hv, scalar_positive _ _ (fun _ => Nat.succ_pos _), ?_⟩
  exact (hs (fun x => ρ x+1) 0).symm

theorem anchorCorrect : Targets.AnchorCorrect := by
  intro Γ hΓ τ t
  obtain ⟨w, hw, c, hc, hs⟩ := actualSourceVectorCompilation [] (by simp) τ
    OrdinalSyntax.defaultPolicy (close hΓ t)
  have hsc := scalar_of_vector w c hc
  have hcode : anchorCode hΓ t = scalarCode (fun _ => 0) c.scalar := by
    simp only [anchorCode, hw, hsc]
  have hav : anchor hΓ t = c.scalar.value (fun _ => 1) := by
    rw [anchor, hcode, encodedScalarSourceCorrect]
    rfl
  have heval : closedSourceValue (SyntaxCode.encodeTerm (close hΓ t)) = anchor hΓ t := by
    rw [hav]
    exact numeric_evaluator_exact _ w c hw hc
  have hvalue : ∀ ν : OrdinalComponent [] → Ordinal,
      denote ν (w 0) = (anchor hΓ t : Ordinal) := by
    intro ν
    have hn : ν = (fun _ => ((1 : Nat) : Ordinal)) := by
      funext z
      rcases z with ⟨σ, x, i⟩
      nomatch x
    rw [hn, hav]
    exact (hs (fun _ => 1) 0).symm
  have hopen : openSourceValue (Γ.length, SyntaxCode.encodeTerm t) = anchor hΓ t := by
    obtain ⟨v, hv, d, hd, hvs⟩ := actualSourceVectorCompilation Γ hΓ τ OrdinalSyntax.defaultPolicy t
    have he := numeric_evaluator_exact t v d hv hd
    rw [ground_codes Γ hΓ] at he
    change openSourceValue (Γ.length, SyntaxCode.encodeTerm t) = d.scalar.value (fun _ => 1) at he
    rw [he]
    have hclose := GroundClosing.Proof.assignmentNaturality Γ [] τ (closingMap hΓ)
      OrdinalSyntax.defaultPolicy t
    rw [hv] at hclose
    change assignment OrdinalSyntax.defaultPolicy (close hΓ t) =
      some (GroundClosing.vector (closingMap hΓ) v) at hclose
    have hwv := Option.some.inj (hw.symm.trans hclose)
    have hval := hvalue (fun _ => 1)
    rw [hwv] at hval
    change denote (fun _ => 1) (GroundClosing.expression (closingMap hΓ) (v 0)) = _ at hval
    rw [closing_value] at hval
    have hvv : (d.scalar.value (fun _ => 1) : Ordinal) = denote (fun _ => 1) (v 0) := by
      simpa only [CompiledVector.value, Fin.cases_zero, Nat.cast_one] using hvs (fun _ => 1) 0
    exact Nat.cast_injective (hvv.trans hval)
  exact ⟨w, c.scalar, hw, hsc, hcode, heval, hopen,
    by rw [hav]; exact scalar_positive _ _ (fun _ => Nat.zero_lt_one), hvalue⟩
end LogicLineages.OrdinalComparison.Source.AbsoluteObserver.Proof
