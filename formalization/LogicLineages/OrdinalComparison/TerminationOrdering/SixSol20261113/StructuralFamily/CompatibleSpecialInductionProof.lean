module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualOriginalApplicationConfinementProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialInductionProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution SubstitutionEnvironmentSupport SourceConstructorIteration ActualOriginalApplication OriginalSpineActions LambdaSpineActions ActualOriginalApplicationSupportProof ActualOriginalApplicationConfinementProof InterpretedArgumentAppend

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem ordinarySuccess (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) {Γ Δ types : List Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f)) (hq : Confined I (.ordinary f base))
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (τ : Ty) (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args)
    (h : headResult f=arrows types τ) (hn : types≠[])
    (hr : Confined I (.marked f τ (substituteArguments base s) types args))
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (he : Agreement M s hs ρ η) :
    interpret ⟨.marked f τ (substituteArguments base s) types args,hr⟩ M P η=
      scan ⟨.ordinary f base,hq⟩ M P ρ (fun {_} _ => true) types τ (argumentValues args ha M P η) h := by
  simp only [scan,action,buildTerm,FunctionalSpineActionsProof.ordinaryAction,FunctionalSpineActionsProof.assembleAction,
    functionalScan,dif_neg hn]
  apply congrArg (M.val ⟨f,hq.2.1⟩ ⟨τ,hr.1.1⟩ P)
  apply Prod.ext
  · exact CompatibleSpecialSupportProof.argumentSubstitution M hcompat base ⟨hq.1.2,hq.2.2⟩ s hs ⟨hr.1.2.1,hr.2.2.1⟩ P ρ η he
  · exact congrArg (TypedExtraAppendProof.appendExtras (OrdinaryFunctionalValue.emptyExtras I P))
      (tuplePacking ⟨headResult f,hq.1.1⟩ args ha h hn M P η).symm

theorem markedSuccess (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) {Γ Δ types : List Ty}
    (f : Head Symbol) (σ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (hq : Confined I (.marked f σ base extraTypes extras))
    (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (τ : Ty) (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args)
    (h : σ=arrows types τ) (hn : types≠[])
    (hr : Confined I (.marked f τ (substituteArguments base s) (extraTypes++types) (appendArguments (substituteArguments extras s) args)))
    (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P) (he : Agreement M s hs ρ η) :
    interpret ⟨.marked f τ (substituteArguments base s) (extraTypes++types) (appendArguments (substituteArguments extras s) args),hr⟩ M P η=
      scan ⟨.marked f σ base extraTypes extras,hq⟩ M P ρ (fun {_} _ => true) types τ (argumentValues args ha M P η) h := by
  have hx := ConfinedSubstitutionProof.argumentClosure Symbol inferInstance arity I Γ Δ extraTypes extras s ⟨hq.1.2.2,hq.2.2.2⟩ hs
  have hp := InterpretedArgumentAppendProof.orderedPackedAppend Symbol inferInstance arity I Δ extraTypes types
    (substituteArguments extras s) args hx ha ⟨hr.1.2.2,hr.2.2.2⟩ M P η
  have heval := CompatibleSpecialSupportProof.argumentSubstitution M hcompat extras ⟨hq.1.2.2,hq.2.2.2⟩ s hs hx P ρ η he
  have hpack : packedValues (substituteArguments extras s) hx M P η=
      packedValues extras ⟨hq.1.2.2,hq.2.2.2⟩ M P ρ :=
    congrArg (packArguments extraTypes (argumentTypeList extras ⟨hq.1.2.2,hq.2.2.2⟩)) heval
  have ht := tuplePacking ⟨σ,hq.1.1⟩ args ha h hn M P η
  simp only [scan,action,buildTerm,FunctionalSpineActionsProof.markedAction,FunctionalSpineActionsProof.assembleAction,
    functionalScan,dif_neg hn]
  apply congrArg (M.val ⟨f,hq.2.1⟩ ⟨τ,hr.1.1⟩ P)
  apply Prod.ext
  · exact CompatibleSpecialSupportProof.argumentSubstitution M hcompat base ⟨hq.1.2.1,hq.2.2.1⟩ s hs ⟨hr.1.2.1,hr.2.2.1⟩ P ρ η he
  · exact (congrArg (TypedExtraAppendProof.appendExtras (OrdinaryFunctionalValue.emptyExtras I P))
      (hp.trans (congrArg₂ List.append hpack ht.symm))).trans
      (InterpretedArgumentAppendProof.downclosureAppend Symbol inferInstance arity I P
        (OrdinaryFunctionalValue.emptyExtras I P) _ _).symm

theorem success (M : Constructors I) (hcompat : Compatible.CurrentTupleCompatible M) {Γ : List Ty} {σ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) :
    ∀ (hq : Confined I q) {Δ types : List Ty} {τ : Ty} (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
      (args : Arguments Symbol arity Δ types) (ha : ArgumentsConfined I args) (h : σ=arrows types τ)
      (r : MarkedTerm Symbol arity Δ τ) (hr : Confined I r),applyOriginalWith q s args h=some r →
      ∀ (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P),Agreement M s hs ρ η →
      interpret ⟨r,hr⟩ M P η=scan ⟨q,hq⟩ M P ρ (fun {_} _ => true) types τ (argumentValues args ha M P η) h := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro hq Δ types τ s hs args ha h r hr heq P ρ η he
    cases args with
    | nil => exact CompatibleSpecialSupportProof.emptySuccess M hcompat ⟨.var v,hq⟩ s hs h r hr heq P ρ η he
    | cons a rest => simp [applyOriginalWith] at heq
  | lam body ih =>
    intro hq Δ types τ s hs args ha h r hr heq P ρ η he
    cases args with
    | nil => exact CompatibleSpecialSupportProof.emptySuccess M hcompat ⟨.lam body,hq⟩ s hs h r hr heq P ρ η he
    | cons a rest =>
      let ac := transportConfined (Ty.arrow.inj h).1.symm a ⟨ha.1.1,ha.2.1⟩
      have hi := ih ⟨hq.1.2.2,hq.2⟩ _ (rangeExtend s hs _ ac) rest ⟨ha.1.2,ha.2.2⟩ (Ty.arrow.inj h).2 r hr heq P
        (extend (interpret ⟨transportTerm (Ty.arrow.inj h).1.symm a,ac⟩ M P η) ρ) η
        (agreementExtend M s hs _ ac P ρ η he)
      have hv := transportInterpret (Ty.arrow.inj h).1.symm a ⟨ha.1.1,ha.2.1⟩ ac M P η
      have hv0 : interpret ⟨a,⟨ha.1.1,ha.2.1⟩⟩ M P η=
          argumentValues (.cons a rest) ha M P η ⟨0,by simp⟩ := rfl
      have henv : @Eq (Environment I _ P)
          (extend (interpret ⟨transportTerm (Ty.arrow.inj h).1.symm a,ac⟩ M P η) ρ)
          (extend (castValue (Ty.arrow.inj h).1.symm (argumentValues (.cons a rest) ha M P η ⟨0,by simp⟩)) ρ) := by
        funext χ v
        cases v with
        | here => exact hv.trans (congrArg (castValue _) hv0)
        | there v => rfl
      exact hi.trans (congrArg₂ (fun (env : Environment I _ P) (mask : Protected _) => (buildTerm I body ⟨hq.1.2.2,hq.2⟩).scan M P env mask
        _ τ (argumentValues rest ⟨ha.1.2,ha.2.2⟩ M P η) (Ty.arrow.inj h).2)
        henv protectAll.symm)
  | ordinary f base ih =>
    intro hq Δ types τ s hs args ha h r hr heq P ρ η he
    cases args with
    | nil => exact CompatibleSpecialSupportProof.emptySuccess M hcompat ⟨.ordinary f base,hq⟩ s hs h r hr heq P ρ η he
    | cons a rest =>
      cases Option.some.inj heq
      exact ordinarySuccess M hcompat f base hq s hs τ (.cons a rest) ha h (by simp) hr P ρ η he
  | marked f output base ts extras ihb ihe =>
    intro hq Δ types τ s hs args ha h r hr heq P ρ η he
    cases args with
    | nil => exact CompatibleSpecialSupportProof.emptySuccess M hcompat ⟨.marked f output base ts extras,hq⟩ s hs h r hr heq P ρ η he
    | cons a rest =>
      cases Option.some.inj heq
      exact markedSuccess M hcompat f output base ts extras hq s hs τ (.cons a rest) ha h (by simp) hr P ρ η he
  | nil => trivial
  | cons q rest ihq ihr => trivial


end LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialInductionProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.SixSol20261113.StructuralFamily.CompatibleSpecialInductionProof
