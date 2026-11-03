module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration ActualOriginalApplication OriginalSpineActions LambdaSpineActions

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem emptyEquation {Γ Δ : List Ty} {σ τ : Ty} (q : MarkedTerm Symbol arity Γ σ)
    (s : MarkedSubstitution Symbol arity Γ Δ) (h : σ=τ) :
    applyOriginalWith q s (.nil : Arguments Symbol arity Δ []) h=some (transportTerm h (substituteTerm q s)) := by
  cases q <;> rfl

theorem transportConfined {Γ : List Ty} {σ τ : Ty} (h : σ=τ) (q : MarkedTerm Symbol arity Γ σ) (hq : Confined I q) :
    Confined I (transportTerm h q) := by cases h; exact hq

theorem rangeExtend {Γ Δ : List Ty} {σ : Ty} (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (a : MarkedTerm Symbol arity Δ σ) (ha : Confined I a) : RangeConfined I (extendEnvironment s a) := by
  intro τ v ht
  cases v with
  | here => exact ha
  | there v => exact hs v ht

theorem transportInterpret {Γ : List Ty} {σ τ : Ty} (h : σ=τ) (q : MarkedTerm Symbol arity Γ σ)
    (hq : Confined I q) (hr : Confined I (transportTerm h q)) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) :
    interpret ⟨transportTerm h q,hr⟩ M P ρ=castValue h (interpret ⟨q,hq⟩ M P ρ) := by
  cases h
  rfl

theorem agreementExtend {Γ Δ : List Ty} {σ : Ty} (M : Constructors I)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (a : MarkedTerm Symbol arity Δ σ) (ha : Confined I a) (P : World I)
    (ρ : Environment I Γ P) (η : Environment I Δ P) (he : Agreement M s hs ρ η) :
    Agreement M (extendEnvironment s a) (rangeExtend s hs a ha) (extend (interpret ⟨a,ha⟩ M P η) ρ) η := by
  intro τ v ht
  cases v with
  | here => rfl
  | there v => exact he v ht

theorem protectAll {Γ : List Ty} {σ : Ty} :
    @Eq (Protected (σ::Γ)) (protectExtend (fun {_} _ => true)) (fun {_} _ => true) := by
  funext τ v
  cases v <;> rfl

theorem argumentSubstitution (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ Δ types : List Ty}
    (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (hr : ArgumentsConfined I (substituteArguments args s)) (P : World I)
    (ρ : Environment I Γ P) (η : Environment I Δ P) (he : Agreement (limit I above) s hs ρ η) :
    argumentValues (substituteArguments args s) hr (limit I above) P η=argumentValues args ha (limit I above) P ρ := by
  induction types with
  | nil => funext i; exact Fin.elim0 i
  | cons τ types ih =>
    cases args with
    | cons q rest =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ActualLimitSubstitutionProof.interpretationSubstitution Symbol inferInstance arity I above inferInstance Γ Δ τ
          ⟨q,⟨ha.1.1,ha.2.1⟩⟩ s hs P ρ η he
      · exact congrFun (ih rest ⟨ha.1.2,ha.2.2⟩ ⟨hr.1.2,hr.2.2⟩) j

theorem tuplePacking {Γ types : List Ty} {τ : Ty} (tag : TypedExtraDownsets.TypeIndex I)
    (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (h : tag.val=arrows types τ) (hn : types≠[]) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) :
    FullTuplePacking.packTuple tag (sourceSuffix tag types τ h hn) (argumentValues args ha M P ρ)=
      InterpretedArgumentAppend.packedValues args ha M P ρ := by
  unfold FullTuplePacking.packTuple InterpretedArgumentAppend.packedValues packArguments
  congr 1

theorem emptySuccess (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ Δ : List Ty} {σ τ : Ty}
    (q : ConfinedTerm I Γ σ) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (h : σ=arrows [] τ) (r : MarkedTerm Symbol arity Δ τ) (hr : Confined I r)
    (heq : applyOriginalWith q.val s (.nil : Arguments Symbol arity Δ []) h=some r)
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (he : Agreement (limit I above) s hs ρ η) :
    interpret ⟨r,hr⟩ (limit I above) P η=scan q (limit I above) P ρ (fun {_} _ => true) [] τ
      (argumentValues (I := I) (.nil : Arguments Symbol arity Δ []) ⟨trivial,trivial⟩ (limit I above) P η) h := by
  cases h
  rw [emptyEquation] at heq
  cases Option.some.inj heq
  exact (ActualLimitSubstitutionProof.interpretationSubstitution Symbol inferInstance arity I above inferInstance Γ Δ τ q s hs P ρ η he).trans
    ((action q).scanEmpty (limit I above) P ρ (fun {_} _ => true) _).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationSupportProof
