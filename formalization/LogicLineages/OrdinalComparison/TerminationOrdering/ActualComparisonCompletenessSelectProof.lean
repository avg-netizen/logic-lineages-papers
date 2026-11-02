module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessOrdinaryProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessSelectProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration ActualComparisonCompleteness RenamingEquivariance FunctionalSpineActions OrdinaryFunctionalValue ActualComparisonCompletenessSupportProof ActualComparisonCompletenessOrdinaryProof ConfinedSubstitution SubstitutionEnvironmentSupport ActualOriginalApplication MarkedSelectTest

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem renameArgsConfined {Γ Δ types : List Ty} (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (r : Renaming Γ Δ) : ArgumentsConfined I (renameArguments args r) := by
  induction types with
  | nil => cases args; exact ⟨trivial,trivial⟩
  | cons τ types ih =>
    cases args with
    | cons q rest =>
      have hq := (StructuralRenaming.renameSource r (⟨q,⟨ha.1.1,ha.2.1⟩⟩ : ConfinedTerm I Γ τ)).property
      have hr := ih rest ⟨ha.1.2,ha.2.2⟩
      exact ⟨⟨hq.1,hr.1⟩,⟨hq.2,hr.2⟩⟩

theorem renameArgsValues {Γ Δ types : List Ty} (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (r : Renaming Γ Δ) (M : Constructors I) (P : World I) (ρ : Environment I Δ P) :
    argumentValues (renameArguments args r) (renameArgsConfined args ha r) M P ρ=argumentValues args ha M P (reindex r ρ) := by
  induction types with
  | nil => funext i; exact Fin.elim0 i
  | cons τ types ih =>
    cases args with
    | cons q rest =>
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact StructuralRenamingProof.interpretationCovariance Symbol inferInstance arity I Γ Δ τ r ⟨q,⟨ha.1.1,ha.2.1⟩⟩ M P ρ
      · exact congrFun (ih rest ⟨ha.1.2,ha.2.2⟩) j

theorem namedApplication (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ types : List Ty} {σ τ : Ty}
    (q : MarkedTerm Symbol arity Γ σ) (hq : Confined I q) (args : Arguments Symbol arity Γ types) (ha : ArgumentsConfined I args)
    (h : σ=arrows types τ) (out : MarkedTerm Symbol arity Γ τ) (hout : Confined I out)
    (happ : applyOriginalWith q (fun {_} v => .var v) args h=some out)
    (P : World I) (r : Renaming Γ (portTypes P.val++I.context)) :
    applyWith (interpret ⟨q,hq⟩ (limit I above) P (reindex r (identity I P))) types τ
      (argumentValues args ha (limit I above) P (reindex r (identity I P))) h=
      interpret ⟨out,hout⟩ (limit I above) P (reindex r (identity I P)) := by
  let env : MarkedSubstitution Symbol arity Γ (portTypes P.val++I.context) := fun {_} v => .var (r v)
  have henv : RangeConfined I env := fun {_} v ht => ⟨ht,trivial⟩
  have hag : Agreement (limit I above) env henv (reindex r (identity I P)) (identity I P) := by intro τ v ht; rfl
  have hc := RenamingEquivarianceProof.originalApplyCovariance Symbol arity Γ Γ Γ _ σ τ types q args
    (fun v => v) r (fun {_} v => .var v) env h (fun {_} v => rfl)
  rw [Source.SourceMarkedBindingProof.markedRenamingIdentity.1 Symbol arity Γ σ q,happ] at hc
  have hqv := ActualLimitApplicationProof.fullApplication Symbol inferInstance arity I above inferInstance Γ σ ⟨q,hq⟩ P
    (reindex r (identity I P)) types τ (argumentValues args ha (limit I above) P (reindex r (identity I P))) h
  have hm := LiteralSpecialApplicationValueProof.scannerMaskAgreement Symbol inferInstance arity I Γ σ ⟨q,hq⟩ (limit I above) P
    (reindex r (identity I P)) (fun {_} _ => false) (fun {_} _ => true)
    (fun {_} v => Or.inr (LiteralSpecialApplicationValueProof.variableBottom (r v))) types τ
    (argumentValues args ha (limit I above) P (reindex r (identity I P))) h
  have hs := ActualOriginalApplicationProof.successInterpretation Symbol inferInstance arity I above inferInstance Γ _ σ ⟨q,hq⟩ env henv
    types τ (renameArguments args r) (renameArgsConfined args ha r) h P (reindex r (identity I P)) (identity I P) hag
    (renameTerm out r) (StructuralRenaming.renameSource r (⟨out,hout⟩ : ConfinedTerm I Γ τ)).property hc
  have hv := congrArg (fun values : Values I types P => scan ⟨q,hq⟩ (limit I above) P (reindex r (identity I P)) (fun {_} _ => true) types τ values h)
    (renameArgsValues args ha r (limit I above) P (identity I P))
  exact hqv.trans (hm.trans (hv.symm.trans (hs.symm.trans
    (StructuralRenamingProof.interpretationCovariance Symbol inferInstance arity I Γ _ τ r ⟨out,hout⟩ (limit I above) P (identity I P)))))

theorem selfConfined {Γ : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (hf : f ∈ headList I)
    (hb : ArgumentsConfined I base) (hx : ArgumentsConfined I extras) (types : List Ty)
    (ht : ∀ τ ∈ types,τ ∈ TypedExtraDownsets.types I) : ArgumentsConfined I (selfArguments f base extraTypes extras types) := by
  induction types with
  | nil => exact ⟨trivial,trivial⟩
  | cons τ types ih =>
    have hr := ih (fun υ hυ => ht υ (List.mem_cons_of_mem _ hυ))
    exact ⟨⟨⟨ht τ List.mem_cons_self,hb.1,hx.1⟩,hr.1⟩,⟨⟨hf,hb.2,hx.2⟩,hr.2⟩⟩

theorem selfValues {Γ : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (hf : f ∈ headList I)
    (hb : ArgumentsConfined I base) (hx : ArgumentsConfined I extras) (types : List Ty)
    (ht : ∀ τ ∈ types,τ ∈ TypedExtraDownsets.types I) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) :
    argumentValues (selfArguments f base extraTypes extras types) (selfConfined f base extraTypes extras hf hb hx types ht) M P ρ=
      fun i => M.val ⟨f,hf⟩ ⟨types.get i,ht _ (List.get_mem _ _)⟩ P
        (markedState ⟨f,hf⟩ (buildArguments I base hb) extraTypes (argumentTypeList extras hx) (buildArguments I extras hx) M P ρ) := by
  induction types with
  | nil => funext i; exact Fin.elim0 i
  | cons τ types ih =>
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact congrFun (ih (fun υ hυ => ht υ (List.mem_cons_of_mem _ hυ))) j

theorem selectedSource {Γ : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (hf : f ∈ headList I)
    (hb : ArgumentsConfined I base) (hx : ArgumentsConfined I extras) (q : RecursiveComparison.Packed Symbol arity Γ)
    (hq : q ∈ argumentList base++argumentList extras) (M : Constructors I) (P : World I) (ρ : Environment I Γ P) :
    ∃ hc : Confined I q.2,Selected ⟨f,hf⟩
      (markedState ⟨f,hf⟩ (buildArguments I base hb) extraTypes (argumentTypeList extras hx) (buildArguments I extras hx) M P ρ)
      (sourceValue q hc M P ρ) := by
  rcases List.mem_append.mp hq with hm | hm
  · rcases leftWitness (baseMatch M P ρ ⟨f,hf⟩ base hb) hm with ⟨v,hv,hmatch⟩
    rcases hmatch with ⟨hc,rfl⟩
    exact ⟨hc,Or.inl hv⟩
  · rcases leftWitness (argumentsMatch extras hx M P ρ) hm with ⟨v,hv,hmatch⟩
    rcases hmatch with ⟨hc,rfl⟩
    refine ⟨hc,Or.inr ?_⟩
    exact TypedExtraAppendProof.suppliedIncluded Symbol inferInstance arity I P (emptyExtras I P) _ _ hv

theorem selectCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} {σ τ : Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Γ extraTypes) (types : List Ty) (q : MarkedTerm Symbol arity Γ σ)
    (out target : MarkedTerm Symbol arity Γ τ) (h : σ=arrows types τ)
    (hselected : (⟨σ,q⟩ : RecursiveComparison.Packed Symbol arity Γ) ∈ argumentList base++argumentList extras)
    (happ : applyOriginalWith q (fun {_} v => .var v) (selfArguments f base extraTypes extras types) h=some out)
    (hm : Meaning (I := I) above false ⟨τ,out⟩ ⟨τ,target⟩) :
    Meaning (I := I) above false ⟨τ,.marked f τ base extraTypes extras⟩ ⟨τ,target⟩ := by
  intro P r hs o ho hp he
  let ρ : Environment I Γ P := reindex r (identity I P)
  let a := markedState ⟨f,hs.2.1⟩ (buildArguments I base ⟨hs.1.2.1,hs.2.2.1⟩) extraTypes
    (argumentTypeList extras ⟨hs.1.2.2,hs.2.2.2⟩) (buildArguments I extras ⟨hs.1.2.2,hs.2.2.2⟩) (limit I above) P ρ
  obtain ⟨hq,hsel⟩ := selectedSource f base extraTypes extras hs.2.1 ⟨hs.1.2.1,hs.2.2.1⟩ ⟨hs.1.2.2,hs.2.2.2⟩
    ⟨σ,q⟩ hselected (limit I above) P ρ
  have hσ := FiniteQueryPrimitivesSupportProof.rootType q hq.1
  have ht : ∀ υ ∈ types,υ ∈ TypedExtraDownsets.types I :=
    (FiniteQueryPrimitivesSupportProof.suffixTypes (fun _ hτ _ hυ => FullTuplePacking.sourceTypeClosed I hτ hυ) types τ (h ▸ hσ)).1
  let hself := selfConfined f base extraTypes extras hs.2.1 ⟨hs.1.2.1,hs.2.2.1⟩ ⟨hs.1.2.2,hs.2.2.2⟩ types ht
  have hout := ActualOriginalApplicationConfinementProof.applicationConfined q hq (fun {_} v => .var v)
    LiteralSpecialApplicationValueProof.identityRange (selfArguments f base extraTypes extras types) hself h out happ
  have hread := hm P r hout o ho hp he
  have hvalue := namedApplication above q hq (selfArguments f base extraTypes extras types) hself h out hout happ P r
  have htype : o.resultType=τ := (congrArg Sigma.fst he).symm
  have htest : selectTest (limit I above) ⟨f,hs.2.1⟩ a o=true := by
    apply (MarkedSelectTestProof.selectCalibration Symbol inferInstance arity I (limit I above) ⟨f,hs.2.1⟩ P a o).mpr
    refine ⟨sourceValue ⟨σ,q⟩ hq (limit I above) P ρ,hsel,?_⟩
    by_cases hn : types=[]
    · subst types
      cases h
      exact Or.inl ⟨htype.symm,(congrArg (fun x => readBit false x o) hvalue).trans hread⟩
    · let suffix := sourceSuffix (⟨σ,hσ⟩ : TypedExtraDownsets.TypeIndex I) types τ h hn
      have hvalues : argumentValues (selfArguments f base extraTypes extras types) hself (limit I above) P ρ=
          selfTuple (limit I above) ⟨f,hs.2.1⟩ a ⟨σ,hσ⟩ suffix :=
        selfValues f base extraTypes extras hs.2.1 ⟨hs.1.2.1,hs.2.2.1⟩ ⟨hs.1.2.2,hs.2.2.2⟩ types ht (limit I above) P ρ
      have hv := (ActualLimitApplicationSupportProof.withSuffix (interpret ⟨q,hq⟩ (limit I above) P ρ) types τ
        (argumentValues (selfArguments f base extraTypes extras types) hself (limit I above) P ρ) h hn).symm.trans hvalue
      have heval : applyValue (interpret ⟨q,hq⟩ (limit I above) P ρ) suffix (selfTuple (limit I above) ⟨f,hs.2.1⟩ a ⟨σ,hσ⟩ suffix)=
          interpret ⟨out,hout⟩ (limit I above) P ρ :=
        (congrArg (applyValue (interpret ⟨q,hq⟩ (limit I above) P ρ) suffix) hvalues.symm).trans hv
      exact Or.inr ⟨suffix,htype.symm,(congrArg (fun x => readBit false x o) heval).trans hread⟩
  apply markedRule above ⟨f,hs.2.1⟩ ⟨τ,hs.1.1⟩ P a o ho hp htype
  simp only [htest,Bool.true_or]

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessSelectProof
