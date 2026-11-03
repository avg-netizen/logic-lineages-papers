module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorProof
public import LogicLineages.OrdinalComparison.SourceTypeSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RecursiveComparison LiteralContexts NativeRecursor NativeCarrier

private theorem restoreRenaming {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : ∀ (Δ : List Ty) (ρ : Renaming Γ Δ)
    (env : MarkedSubstitution Symbol arity Δ Γ), (∀ {σ} (v : Variable Γ σ),env (ρ v)=.var v) →
    substituteTerm (renameTerm q ρ) env=q := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ (Δ : List Ty) (ρ : Renaming Γ Δ)
      (env : MarkedSubstitution Symbol arity Δ Γ), (∀ {σ} (v : Variable Γ σ),env (ρ v)=.var v) →
      substituteArguments (renameArguments args ρ) env=args) with
  | var v => intro Δ ρ env h; exact h v
  | lam body ih =>
      intro Δ ρ env h
      apply congrArg MarkedTerm.lam
      apply ih _ ρ.lift (liftSubstitution env)
      intro σ v
      cases v with
      | here => rfl
      | there v => simp only [Renaming.lift,liftSubstitution,h,renameTerm,Renaming.weaken]
  | ordinary hd args ih =>
      intro Δ ρ env h
      exact congrArg (MarkedTerm.ordinary hd) (ih Δ ρ env h)
  | marked hd out args types extras iha ihe =>
      intro Δ ρ env h
      exact congrArg₂ (fun a e => MarkedTerm.marked hd out a types e) (iha Δ ρ env h) (ihe Δ ρ env h)
  | nil => rfl
  | cons q rest ihq ihr =>
      rename_i Δ ρ env h
      exact congrArg₂ Arguments.cons (ihq Δ ρ env h) (ihr Δ ρ env h)

private theorem emptyWith {Symbol : Type} {arity : Symbol → Nat} {Γ Δ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) (env : MarkedSubstitution Symbol arity Γ Δ) :
    applyOriginalWith q env .nil rfl=some (substituteTerm q env) := by
  cases q <;> rfl

theorem unusedConsumption {Symbol : Type} {arity : Symbol → Nat} {B : Ty}
    (K : Term Symbol arity [] (.arrow B B)) (a : MarkedTerm Symbol arity [] .ground) :
    applyOriginalWith (embed (unusedGroundStep K)) (fun v => .var v) (.cons a .nil) rfl=some (embed K) := by
  change applyOriginalWith (embed (K.rename (Renaming.weaken [] .ground)))
    (extendEnvironment (fun v => .var v) a) .nil rfl = _
  rw [emptyWith,Source.SourceMarkedBindingProof.embeddingRenaming]
  apply congrArg some
  apply restoreRenaming
  intro σ v
  cases v

variable {Symbol : Type} {arity : Symbol → Nat} {B : Ty}
variable (K : Term Symbol arity [] (.arrow B B)) (U : Term Symbol arity [] B)

def outer (ρ : Ty) : MarkedTerm Symbol arity [] ρ :=
  .marked (.application B B) ρ
    (.cons (embed (.app (.app (.recC B) .zeroC) (unusedGroundStep K))) (.cons (embed U) .nil)) [] .nil

def middle (ρ : Ty) : MarkedTerm Symbol arity [] ρ :=
  .marked (.application (stepType B) (.arrow B B)) ρ
    (.cons (embed (.app (.recC B) .zeroC)) (.cons (embed (unusedGroundStep K)) .nil)) [B] (.cons (outer K U B) .nil)

def inner (ρ : Ty) : MarkedTerm Symbol arity [] ρ :=
  .marked (.application .ground (.arrow (stepType B) (.arrow B B))) ρ
    (.cons (embed (.recC B)) (.cons (embed (.zeroC)) .nil)) [stepType B,B]
    (.cons (middle K U (stepType B)) (.cons (middle K U B) .nil))

def native (ρ : Ty) : MarkedTerm Symbol arity [] ρ :=
  .marked (.recursor B) ρ .nil [.ground,stepType B,B]
    (.cons (inner K U .ground) (.cons (inner K U (stepType B)) (.cons (inner K U B) .nil)))

variable (above : Symbol → Symbol → Prop)

theorem outerPrefixes (t : MarkedTerm Symbol arity [] B)
    (h : Weak Symbol arity above [] ⟨B,native K U B⟩ ⟨B,t⟩) :
    Weak Symbol arity above [] ⟨B,outer K U B⟩ ⟨B,t⟩ := by
  apply Weak.select _ _ _ _ [B]
    (embed (.app (.app (.recC B) .zeroC) (unusedGroundStep K))) (middle K U B) t rfl
  · simp [outer,argumentList]
  · simp only [embed,applyOriginalWith,selfArguments,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2]; rfl
  · apply Weak.select _ _ _ _ [stepType B,B]
      (embed (.app (.recC B) .zeroC)) (inner K U B) t rfl
    · simp [middle,argumentList]
    · simp only [embed,applyOriginalWith,selfArguments,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2]; rfl
    · apply Weak.select _ _ _ _ [.ground,stepType B,B] (embed (.recC B)) (native K U B) t rfl
      · exact List.mem_append.mpr (Or.inl List.mem_cons_self)
      · rfl
      · exact h

theorem extraChain (t : MarkedTerm Symbol arity [] B)
    (h : Weak Symbol arity above [] ⟨B,outer K U B⟩ ⟨B,t⟩) :
    Weak Symbol arity above [] ⟨B,native K U B⟩ ⟨B,t⟩ := by
  apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above [] _ _ _ _ B (inner K U B) t
  · simp [native,argumentList]
  · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above [] _ _ _ _ B (middle K U B) t
    · simp [inner,argumentList]
    · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above [] _ _ _ _ B (outer K U B) t
      · simp [middle,argumentList]
      · exact h

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierSupportProof
