module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesSyntaxProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceFreeOccurrences
open RecursiveComparison ComparisonFreeVariables

private theorem binderOccurrences {Γ : List Ty} {σ : Ty} (xs : List (PackedVariable (σ::Γ))) (a : Allowed Γ) :
    (∀ v ∈ xs, liftAllowed a v.2) ↔ ∀ v ∈ xs.filterMap dropBound, a v.2 := by
  constructor
  · intro h v hv
    obtain ⟨⟨υ,w⟩,hw,he⟩ := List.mem_filterMap.mp hv
    cases w with
    | here => cases he
    | there w =>
        have he' : (⟨υ,w⟩ : PackedVariable Γ)=v := Option.some.inj he
        subst v
        exact h ⟨υ,.there w⟩ hw
  · intro h v hv
    rcases v with ⟨υ,v⟩
    cases v with
    | here => trivial
    | there v => exact h ⟨υ,v⟩ (List.mem_filterMap.mpr ⟨⟨υ,.there v⟩,hv,rfl⟩)

theorem supportCalibration : ComparisonFreeVariablesTargets.SupportCalibration := by
  intro Symbol arity Γ τ q
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ a : Allowed Γ, ArgumentsSupported args a ↔ ∀ v ∈ argumentOccurrences args,a v.2) with
  | var v => intro a; simp [Supported,markedOccurrences]
  | lam body ih =>
      intro a
      change Supported body (liftAllowed a) ↔ _
      rw [ih]
      exact binderOccurrences _ a
  | ordinary hd base ih => exact ih
  | marked hd out base types extras ihb ihe =>
      intro a
      simp only [Supported,markedOccurrences,ihb,ihe,List.mem_append]
      constructor
      · intro h v hv; rcases hv with hv | hv; exact h.1 v hv; exact h.2 v hv
      · intro h; exact ⟨fun v hv => h v (Or.inl hv),fun v hv => h v (Or.inr hv)⟩
  | nil => simp [ArgumentsSupported,argumentOccurrences]
  | cons q rest ihq ihr =>
      rename_i a
      simp only [ArgumentsSupported,argumentOccurrences,ihq,ihr,List.mem_append]
      constructor
      · intro h v hv; rcases hv with hv | hv; exact h.1 v hv; exact h.2 v hv
      · intro h; exact ⟨fun v hv => h v (Or.inl hv),fun v hv => h v (Or.inr hv)⟩

private theorem groundOccurrences {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (n : Nat) (f : Fin n → MarkedTerm Symbol arity Γ .ground) :
    argumentOccurrences (groundArguments n f)=(List.ofFn (fun i => markedOccurrences (f i))).flatten := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [groundArguments,argumentOccurrences,List.ofFn_succ,List.flatten_cons,ih]
      rfl

theorem ordinaryOccurrenceCalibration : ComparisonFreeVariablesTargets.OrdinaryOccurrenceCalibration := by
  intro Symbol arity Γ τ t
  induction t with
  | var v => rfl
  | app f a ihf iha => simp only [embed,markedOccurrences,argumentOccurrences,freeOccurrences,ihf,iha,List.append_nil]
  | lam body ih => exact congrArg (List.filterMap dropBound) ih
  | zeroC => rfl
  | succC => rfl
  | caseC τ => rfl
  | recC τ => rfl
  | ranked f args ih =>
      exact (groundOccurrences (arity f) (fun i => embed (args i))).trans
        (congrArg (fun f => (List.ofFn f).flatten) (funext ih))

theorem renameSupported {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : ∀ (a : Allowed Γ),Supported q a →
    ∀ (Δ : List Ty) (ρ : Renaming Γ Δ) (b : Allowed Δ),
    (∀ {υ} (v : Variable Γ υ),a v → b (ρ v)) → Supported (renameTerm q ρ) b := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ (a : Allowed Γ),ArgumentsSupported args a →
      ∀ (Δ : List Ty) (ρ : Renaming Γ Δ) (b : Allowed Δ),
      (∀ {υ} (v : Variable Γ υ),a v → b (ρ v)) → ArgumentsSupported (renameArguments args ρ) b) with
  | var v => intro a h Δ ρ b hb; exact hb v h
  | lam body ih =>
      intro a h Δ ρ b hb
      apply ih (liftAllowed a) h _ ρ.lift (liftAllowed b)
      intro υ v hv
      cases v with
      | here => trivial
      | there v => exact hb v hv
  | ordinary hd base ih => exact ih
  | marked hd out base types extras ihb ihe =>
      intro a h Δ ρ b hb
      exact ⟨ihb a h.1 Δ ρ b hb,ihe a h.2 Δ ρ b hb⟩
  | nil => trivial
  | cons q rest ihq ihr =>
      rename_i a h Δ ρ b hb
      exact ⟨ihq a h.1 Δ ρ b hb,ihr a h.2 Δ ρ b hb⟩

theorem renameArgumentsSupported {Symbol : Type} {arity : Symbol → Nat} {Γ Δ types : List Ty}
    (args : Arguments Symbol arity Γ types) (a : Allowed Γ) (b : Allowed Δ) (ρ : Renaming Γ Δ)
    (h : ArgumentsSupported args a) (hb : ∀ {υ} (v : Variable Γ υ),a v → b (ρ v)) :
    ArgumentsSupported (renameArguments args ρ) b := by
  induction types with
  | nil => cases args; trivial
  | cons σ types ih => cases args with
    | cons q rest => exact ⟨renameSupported q a h.1 Δ ρ b hb,ih rest h.2⟩

theorem substituteSupported {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : ∀ (a : Allowed Γ),Supported q a →
    ∀ (Δ : List Ty) (env : MarkedSubstitution Symbol arity Γ Δ) (b : Allowed Δ),
    (∀ {υ} (v : Variable Γ υ),a v → Supported (env v) b) → Supported (substituteTerm q env) b := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ (a : Allowed Γ),ArgumentsSupported args a →
      ∀ (Δ : List Ty) (env : MarkedSubstitution Symbol arity Γ Δ) (b : Allowed Δ),
      (∀ {υ} (v : Variable Γ υ),a v → Supported (env v) b) → ArgumentsSupported (substituteArguments args env) b) with
  | var v => intro a h Δ env b hb; exact hb v h
  | lam body ih =>
      intro a h Δ env b hb
      apply ih (liftAllowed a) h _ (liftSubstitution env) (liftAllowed b)
      intro υ v hv
      cases v with
      | here => trivial
      | there v => exact renameSupported (env v) b (hb v hv) _ (Renaming.weaken Δ _) (liftAllowed b) (by intros; assumption)
  | ordinary hd base ih => exact ih
  | marked hd out base types extras ihb ihe =>
      intro a h Δ env b hb
      exact ⟨ihb a h.1 Δ env b hb,ihe a h.2 Δ env b hb⟩
  | nil => trivial
  | cons q rest ihq ihr =>
      rename_i a h Δ env b hb
      exact ⟨ihq a h.1 Δ env b hb,ihr a h.2 Δ env b hb⟩

theorem substituteArgumentsSupported {Symbol : Type} {arity : Symbol → Nat} {Γ Δ types : List Ty}
    (args : Arguments Symbol arity Γ types) (a : Allowed Γ) (b : Allowed Δ)
    (env : MarkedSubstitution Symbol arity Γ Δ) (h : ArgumentsSupported args a)
    (hb : ∀ {υ} (v : Variable Γ υ),a v → Supported (env v) b) : ArgumentsSupported (substituteArguments args env) b := by
  induction types with
  | nil => cases args; trivial
  | cons σ types ih => cases args with
    | cons q rest => exact ⟨substituteSupported q a h.1 Δ env b hb,ih rest h.2⟩

theorem appendSupported {Symbol : Type} {arity : Symbol → Nat} {Γ xs ys : List Ty}
    (args : Arguments Symbol arity Γ xs) (extras : Arguments Symbol arity Γ ys) (a : Allowed Γ) :
    ArgumentsSupported (appendArguments args extras) a ↔ ArgumentsSupported args a ∧ ArgumentsSupported extras a := by
  induction xs with
  | nil => cases args; simp [appendArguments,ArgumentsSupported]
  | cons σ xs ih => cases args with
    | cons q rest => simp only [appendArguments,ArgumentsSupported,ih,and_assoc]

theorem argumentsListSupported {Symbol : Type} {arity : Symbol → Nat} {Γ types : List Ty}
    (args : Arguments Symbol arity Γ types) (a : Allowed Γ) :
    ArgumentsSupported args a ↔ ∀ p ∈ argumentList args,Supported p.2 a := by
  induction types with
  | nil => cases args; simp [ArgumentsSupported,argumentList]
  | cons σ types ih => cases args with
    | cons q rest => simp only [ArgumentsSupported,argumentList,List.mem_cons,forall_eq_or_imp,ih]

theorem markSupported {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (q : MarkedTerm Symbol arity Γ τ) : ∀ (r : MarkedTerm Symbol arity Γ τ), strictMark q=some r →
    ∀ a,Supported q a → Supported r a := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v => intro r h; cases h
  | lam body ih =>
      intro r he a hs
      cases hm : strictMark body with
      | none => simp [strictMark,hm] at he
      | some out =>
          have hr : MarkedTerm.lam out=r := Option.some.inj (by simpa only [strictMark,hm,Option.map_some] using he)
          subst r
          exact ih out hm (liftAllowed a) hs
  | ordinary hd base ih =>
      intro r he a hs
      have hr : MarkedTerm.marked hd (headResult hd) base [] .nil=r := Option.some.inj he
      subst r
      exact ⟨hs,trivial⟩
  | marked hd out base types extras ihb ihe => intro r he; cases he
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesSyntaxProof
