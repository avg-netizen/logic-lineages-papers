module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationConfinementProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution ActualOriginalApplication ActualOriginalApplicationSupportProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem emptyConfined {Γ Δ : List Ty} {σ τ : Ty} (q : MarkedTerm Symbol arity Γ σ) (hq : Confined I q)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) (h : σ=τ)
    (r : MarkedTerm Symbol arity Δ τ) (heq : applyOriginalWith q s (.nil : Arguments Symbol arity Δ []) h=some r) : Confined I r := by
  rw [emptyEquation] at heq
  cases Option.some.inj heq
  exact transportConfined h _ (ConfinedSubstitutionProof.substitutionClosure Symbol inferInstance arity I Γ Δ σ q s hq hs)

theorem applicationConfined {Γ : List Ty} {σ : Ty} (q : MarkedTerm Symbol arity Γ σ) :
    ∀ (hq : Confined I q) {Δ types : List Ty} {τ : Ty} (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
      (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args) (h : σ=arrows types τ)
      (r : MarkedTerm Symbol arity Δ τ),applyOriginalWith q s args h=some r → Confined I r := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro hq Δ types τ s hs args ha h r heq
    cases args with
    | nil => exact emptyConfined (.var v) hq s hs h r heq
    | cons a rest => simp [applyOriginalWith] at heq
  | lam body ih =>
    intro hq Δ types τ s hs args ha h r heq
    cases args with
    | nil => exact emptyConfined (.lam body) hq s hs h r heq
    | cons a rest =>
      exact ih ⟨hq.1.2.2,hq.2⟩ _
        (rangeExtend s hs (transportTerm (Ty.arrow.inj h).1.symm a) (transportConfined _ a ⟨ha.1.1,ha.2.1⟩))
        rest ⟨ha.1.2,ha.2.2⟩ (Ty.arrow.inj h).2 r heq
  | ordinary f base ih =>
    intro hq Δ types τ s hs args ha h r heq
    cases args with
    | nil => exact emptyConfined (.ordinary f base) hq s hs h r heq
    | cons a rest =>
      have ht := (FullTuplePacking.resultTag I ⟨headResult f,hq.1.1⟩ (sourceSuffix ⟨headResult f,hq.1.1⟩ _ τ h (by simp))).property
      have hb := ConfinedSubstitutionProof.argumentClosure Symbol inferInstance arity I _ Δ _ base s ⟨hq.1.2,hq.2.2⟩ hs
      cases Option.some.inj heq
      exact ⟨⟨ht,hb.1,ha.1⟩,⟨hq.2.1,hb.2,ha.2⟩⟩
  | marked f output base ts extras ihb ihe =>
    intro hq Δ types τ s hs args ha h r heq
    cases args with
    | nil => exact emptyConfined (.marked f output base ts extras) hq s hs h r heq
    | cons a rest =>
      have ht := (FullTuplePacking.resultTag I ⟨output,hq.1.1⟩ (sourceSuffix ⟨output,hq.1.1⟩ _ τ h (by simp))).property
      have hb := ConfinedSubstitutionProof.argumentClosure Symbol inferInstance arity I _ Δ _ base s ⟨hq.1.2.1,hq.2.2.1⟩ hs
      have he := ConfinedSubstitutionProof.argumentClosure Symbol inferInstance arity I _ Δ _ extras s ⟨hq.1.2.2,hq.2.2.2⟩ hs
      have hap := InterpretedArgumentAppendProof.confinedAppend (substituteArguments extras s) (.cons a rest) he ha
      cases Option.some.inj heq
      exact ⟨⟨ht,hb.1,hap.1⟩,⟨hq.2.1,hb.2,hap.2⟩⟩
  | nil => trivial
  | cons q rest ihq ihr => trivial

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationConfinementProof
