module
public import LogicLineages.OrdinalComparison.SourceNamedSubstitutionTargets
public import LogicLineages.OrdinalComparison.SourceStructural
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceNamedSubstitutionProof
open SourceNamedSyntax SourceNamedSyntaxProof SourceNamedWeakening SourceNamedWeakeningProof
open SourceNamedSubstitution SourceNamedSubstitutionTargets SourceTypeSupport

theorem constructedEnvironmentCalibration : ConstructedEnvironmentCalibration := by
  intro Symbol arity Γ Δ env x σ h
  change erase (env x σ h) = if hh : lookup Γ (variableName (resolve Γ x h)) = some σ then
    erase (env (variableName (resolve Γ x h)) σ hh) else canonicalInhabitant (contextTypes Δ) σ
  simp only [(namedResolution Γ x σ h).1, dif_pos h]

private theorem extend_along {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : Context}
    (env : NamedEnvironment Symbol arity Γ Δ)
    (s : Substitution Symbol arity (contextTypes Γ) (contextTypes Δ))
    (hr : EnvironmentAlong env s) (x : Nat) (σ : Ty) :
    EnvironmentAlong (extendNamedEnvironment env x σ (freshName Δ) (concreteFreshName Δ).1) s.lift := by
  intro z τ h
  by_cases e : z = x
  · subst z
    have ht : σ = τ := by simpa [lookup] using h
    subst τ
    simp only [extendNamedEnvironment, resolve, dif_pos True.intro, erase]
    rfl
  · have hh : lookup Γ z = some τ := by simpa [lookup, e] using h
    simp only [extendNamedEnvironment, dif_neg e, resolve]
    change erase (namedWeaken (freshName Δ) σ (concreteFreshName Δ).1 (env z τ hh)) =
      (s (resolve Γ z hh)).rename (Renaming.weaken (contextTypes Δ) σ)
    obtain ⟨hf, hweak⟩ := actualFreshWeakening Symbol arity Δ σ
    exact (hweak τ (env z τ hh)).1.trans
      (congrArg (fun t => t.rename (Renaming.weaken (contextTypes Δ) σ)) (hr z τ hh))

theorem namedSubstitutionErasureSupplier : NamedSubstitutionErasureSupplier := by
  intro Symbol arity Γ Δ τ t env s hr
  induction t generalizing Δ with
  | var x h => exact hr x _ h
  | app f a ihf iha =>
    change Term.app (erase (namedSubstitute f env)) (erase (namedSubstitute a env)) = _
    rw [ihf _ env s hr, iha _ env s hr]
    rfl
  | lam x body ih =>
    change Term.lam (erase (namedSubstitute body
      (extendNamedEnvironment env x _ (freshName Δ) (concreteFreshName Δ).1))) = _
    rw [ih _ _ _ (extend_along env s hr x _)]
    rfl
  | zeroC | succC | caseC | recC => rfl
  | ranked a args ih =>
    change Term.ranked a (fun i => erase (namedSubstitute (args i) env)) = _
    have he : (fun i => erase (namedSubstitute (args i) env)) =
        (fun i => (erase (args i)).substitute s) := by funext i; exact ih i _ env s hr
    rw [he]
    rfl

theorem actualNamedSubstitutionErasure : ActualNamedSubstitutionErasure := by
  intro Symbol arity Γ Δ τ t env
  exact namedSubstitutionErasureSupplier Symbol arity Γ Δ τ t env _
    (constructedEnvironmentCalibration Symbol arity Γ Δ env)

theorem literalNamedSubstitutionEquations : LiteralNamedSubstitutionEquations := by
  constructor <;> intros <;> rfl

theorem identityNamedSubstitutionFootprint : IdentityNamedSubstitutionFootprint := by
  intro Symbol arity Γ τ t
  let env : NamedEnvironment Symbol arity Γ Γ := fun x _ h => .var x h
  have hr : EnvironmentAlong env (fun v => .var v) := by intro x σ h; rfl
  have he : erase (namedSubstitute t env) = erase t :=
    (namedSubstitutionErasureSupplier Symbol arity Γ Γ τ t env _ hr).trans
      (Term.substitute_identity (erase t))
  have hs := congrArg (typeSupport (Symbol := Symbol) (arity := arity)) he
  have hv := congrArg (fun u : Term Symbol arity (contextTypes Γ) τ =>
    (SourceFreeOccurrences.freeOccurrences u).map (namePacked (Γ := Γ))) he
  have hd := congrArg (lambdaDepth (Symbol := Symbol) (arity := arity)) he
  rw [namedSupportCalibration, namedSupportCalibration] at hs
  rw [namedOccurrenceCalibration, namedOccurrenceCalibration] at hv
  rw [namedDepthCalibration, namedDepthCalibration] at hd
  exact ⟨hs, hv, hd⟩

end LogicLineages.OrdinalComparison.Source.SourceNamedSubstitutionProof
