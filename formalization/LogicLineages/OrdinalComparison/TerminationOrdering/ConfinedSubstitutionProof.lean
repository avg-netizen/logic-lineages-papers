module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitutionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitutionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding FiniteObservationBits OriginalSpineActions ConfinedStructuralInterpretation ComparisonFreeVariables ConfinedSubstitution

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem liftedRange : ConfinedSubstitutionTargets.LiftedRange := by
  intro Symbol inst arity I Γ Δ σ s hs τ v ht
  cases v with
  | here => exact ⟨ht,trivial⟩
  | there v =>
    exact ⟨TypeClosureProof.renameAllowed _ (s v) (Renaming.weaken Δ σ) (hs v ht).1,
      LogicLineages.OrdinalComparison.TerminationOrdering.Proof.renameAllowed _ (s v) (Renaming.weaken Δ σ) (hs v ht).2⟩

theorem substituteConfined {Γ : List Ty} {τ : Ty} (q : MarkedTerm Symbol arity Γ τ) :
    ∀ (Δ : List Ty) (s : MarkedSubstitution Symbol arity Γ Δ),Confined I q → RangeConfined I s → Confined I (substituteTerm q s) := by
  induction q using MarkedTerm.rec
    (motive_2 := fun Γ types args => ∀ (Δ : List Ty) (s : MarkedSubstitution Symbol arity Γ Δ),
      ArgumentsConfined I args → RangeConfined I s → ArgumentsConfined I (substituteArguments args s)) with
  | var v => intro Δ s hq hs; exact hs v hq.1
  | lam body ih =>
    intro Δ s hq hs
    have hb := ih _ (liftSubstitution s) ⟨hq.1.2.2,hq.2⟩
      (liftedRange Symbol inferInstance arity I _ Δ _ s hs)
    exact ⟨⟨hq.1.1,hq.1.2.1,hb.1⟩,hb.2⟩
  | ordinary f base ih =>
    intro Δ s hq hs
    have hb := ih Δ s ⟨hq.1.2,hq.2.2⟩ hs
    exact ⟨⟨hq.1.1,hb.1⟩,hq.2.1,hb.2⟩
  | marked f τ base ts extras ihb ihe =>
    intro Δ s hq hs
    have hb := ihb Δ s ⟨hq.1.2.1,hq.2.2.1⟩ hs
    have he := ihe Δ s ⟨hq.1.2.2,hq.2.2.2⟩ hs
    exact ⟨⟨hq.1.1,hb.1,he.1⟩,hq.2.1,hb.2,he.2⟩
  | nil => exact ⟨trivial,trivial⟩
  | cons q rest ihq ihr =>
    rename_i Δ s ha hs
    have hq := ihq Δ s ⟨ha.1.1,ha.2.1⟩ hs
    have hr := ihr Δ s ⟨ha.1.2,ha.2.2⟩ hs
    exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩

theorem substitutionClosure : ConfinedSubstitutionTargets.SubstitutionClosure := by
  intro Symbol inst arity I Γ Δ τ q s hq hs
  exact substituteConfined q Δ s hq hs

theorem argumentClosure : ConfinedSubstitutionTargets.ArgumentClosure := by
  intro Symbol inst arity I Γ Δ types args s ha hs
  induction types with
  | nil => cases args; exact ⟨trivial,trivial⟩
  | cons τ types ih =>
    cases args with
    | cons q rest =>
      have hq := substituteConfined q Δ s ⟨ha.1.1,ha.2.1⟩ hs
      have hr := ih rest ⟨ha.1.2,ha.2.2⟩
      exact ⟨⟨hq.1,hr.1⟩,hq.2,hr.2⟩

theorem initiallyCompatible : ConfinedSubstitutionTargets.InitiallyCompatible := by
  intro Symbol inst arity I Γ Δ s τ v ht
  constructor
  · intro h; cases h
  · intro _
    apply (ComparisonFreeVariablesSyntaxProof.supportCalibration Symbol arity Δ τ (s v) _).mpr
    intro w hw
    rfl

theorem liftedCompatibility : ConfinedSubstitutionTargets.LiftedCompatibility := by
  intro Symbol inst arity I Γ Δ σ s sourceMask targetMask hs τ v ht
  cases v with
  | here =>
    constructor
    · intro _; exact ⟨Variable.here,rfl,rfl⟩
    · intro h; cases h
  | there v =>
    constructor
    · intro hp
      obtain ⟨w,hw,hm⟩ := (hs v ht).1 hp
      refine ⟨Variable.there w,?_,hm⟩
      simp only [liftSubstitution,hw,renameTerm]
      rfl
    · intro hp
      exact ComparisonFreeVariablesSyntaxProof.renameSupported (s v) (fun {_} w => targetMask w=false)
        ((hs v ht).2 hp) _ (Renaming.weaken Δ σ)
        (fun {_} w => LambdaSpineActions.protectExtend targetMask w=false) (fun {_} _ hw => hw)

theorem literalLift : ConfinedSubstitutionTargets.LiteralLift := by
  intro Symbol inst arity I Γ Δ σ s
  exact ⟨rfl,fun {_} _ => rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedSubstitutionProof
