module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice OriginalSpineActions FunctionalSpineActions ConfinedStructuralInterpretation ConfinedSubstitution ComparisonFreeVariables SubstitutionEnvironmentSupport SourceConstructorIteration ActualLimitSubstitution

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

def Related (M : Constructors I) {Γ Δ : List Ty} {τ : Ty} (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (A : PairedAction I Γ τ) (B : PairedAction I Δ τ) : Prop :=
  ∀ P (ρ : Environment I Γ P) (η : Environment I Δ P),Agreement M s hs ρ η →
    B.evaluate M P η=A.evaluate M P ρ ∧
    ∀ (sourceMask : Protected Γ) (targetMask : Protected Δ),ProtectedCompatible I s sourceMask targetMask →
      ∀ types υ (args : Values I types P) (h : τ=arrows types υ),
        B.scan M P η targetMask types υ args h=A.scan M P ρ sourceMask types υ args h

def ArgumentsRelated (M : Constructors I) {Γ Δ types : List Ty} (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (A : ArgumentActions I Γ types) (B : ArgumentActions I Δ types) : Prop :=
  ∀ P (ρ : Environment I Γ P) (η : Environment I Δ P),Agreement M s hs ρ η →
    evaluateArguments B M P η=evaluateArguments A M P ρ

theorem variableRelated (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ Δ : List Ty} {τ : Ty}
    (v : Variable Γ τ) (ht : τ ∈ TypedExtraDownsets.types I) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s) :
    Related (limit I above) s hs (OriginalSpineActionsProof.variableAction v) (action ⟨s v,hs v ht⟩) := by
  intro P ρ η ha
  refine ⟨(ha v ht).symm,?_⟩
  intro sourceMask targetMask hc types υ args h
  by_cases hn : types=[]
  · subst types
    cases h
    exact ((action (⟨s v,hs v ht⟩ : ConfinedTerm I Δ υ)).scanEmpty (limit I above) P η targetMask args).trans
      ((ha v ht).symm.trans ((OriginalSpineActionsProof.variableAction v).scanEmpty (limit I above) P ρ sourceMask args).symm)
  · cases hv : sourceMask v with
    | false =>
      have hfree := (hc v ht).2 hv
      have hm := SubstitutionEnvironmentSupportProof.maskLocality Symbol inferInstance arity I Δ τ ⟨s v,hs v ht⟩
        (limit I above) P η targetMask (fun {_} _ => false) hfree types υ args h
      have happ := ActualLimitApplicationProof.fullApplication Symbol inferInstance arity I above inferInstance Δ τ
        ⟨s v,hs v ht⟩ P η types υ args h
      have he := congrArg (fun a : Value I τ P => applyWith a types υ args h) (ha v ht).symm
      exact hm.trans (happ.symm.trans (he.trans (by simp [OriginalSpineActionsProof.variableAction,variableScan,hn,hv])))
    | true =>
      obtain ⟨w,hw,hm⟩ := (hc v ht).1 hv
      have hq : (⟨s v,hs v ht⟩ : ConfinedTerm I Δ τ)=⟨.var w,⟨ht,trivial⟩⟩ := Subtype.ext hw
      have he := congrArg (fun q : ConfinedTerm I Δ τ => scan q (limit I above) P η targetMask types υ args h) hq
      exact he.trans (by simp [scan,action,buildTerm,OriginalSpineActionsProof.variableAction,variableScan,hn,hm,hv])

theorem functionalScanEq {Γ Δ : List Ty} (f : HeadIndex I) (τ : TypedExtraDownsets.TypeIndex I)
    (eA : Evaluate I Γ τ.val) (eB : Evaluate I Δ τ.val)
    (stateA : (M : Constructors I) → (P : World I) → Environment I Γ P → Inputs I f P)
    (stateB : (M : Constructors I) → (P : World I) → Environment I Δ P → Inputs I f P)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (η : Environment I Δ P)
    (he : eB M P η=eA M P ρ) (ha : stateB M P η=stateA M P ρ)
    (sourceMask : Protected Γ) (targetMask : Protected Δ) (types : List Ty) (υ : Ty)
    (args : Values I types P) (h : τ.val=arrows types υ) :
    functionalScan f τ eB stateB M P η targetMask types υ args h=
      functionalScan f τ eA stateA M P ρ sourceMask types υ args h := by
  by_cases hn : types=[]
  · simp only [functionalScan,dif_pos hn]
    exact congrArg (Eq.mp _) he
  · simp only [functionalScan,dif_neg hn]
    exact congrArg (fun a : Inputs I f P => M.val f (FullTuplePacking.resultTag I τ (sourceSuffix τ types υ h hn)) P
      (FunctionalTupleBuilder.appendInput a (FullTuplePacking.packTuple τ (sourceSuffix τ types υ h hn) args))) ha

theorem ordinaryRelated {Γ Δ : List Ty} (M : Constructors I) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (f : HeadIndex I) (A : ArgumentActions I Γ (headArguments arity f.val)) (B : ArgumentActions I Δ (headArguments arity f.val))
    (hab : ArgumentsRelated M s hs A B) :
    Related M s hs (FunctionalSpineActionsProof.ordinaryAction f A) (FunctionalSpineActionsProof.ordinaryAction f B) := by
  intro P ρ η ha
  have hb := hab P ρ η ha
  have he := congrArg (OrdinaryFunctionalValue.ordinaryValue M f) hb
  refine ⟨he,?_⟩
  intro sourceMask targetMask hc types υ args h
  exact functionalScanEq f ⟨headResult f.val,OrdinaryFunctionalValueProof.sourceHeadResultTypes Symbol inferInstance arity I f⟩
    (ordinaryEvaluate f A) (ordinaryEvaluate f B) (ordinaryState f A) (ordinaryState f B) M P ρ η he
    (congrArg (fun b : BaseTuple I f P => (b,OrdinaryFunctionalValue.emptyExtras I P)) hb) sourceMask targetMask types υ args h

theorem markedStateEq {Γ Δ : List Ty} (M : Constructors I) (f : HeadIndex I)
    (A : ArgumentActions I Γ (headArguments arity f.val)) (B : ArgumentActions I Δ (headArguments arity f.val))
    (types : List Ty) (ht : ∀ τ ∈ types,τ ∈ TypedExtraDownsets.types I)
    (E : ArgumentActions I Γ types) (F : ArgumentActions I Δ types) (P : World I)
    (ρ : Environment I Γ P) (η : Environment I Δ P)
    (hb : evaluateArguments B M P η=evaluateArguments A M P ρ) (he : evaluateArguments F M P η=evaluateArguments E M P ρ) :
    markedState f B types ht F M P η=markedState f A types ht E M P ρ := by
  exact congrArg₂ (fun (b : BaseTuple I f P) (e : Values I types P) =>
    (b,TypedExtraAppendProof.appendExtras (OrdinaryFunctionalValue.emptyExtras I P) (packArguments types ht e))) hb he

theorem markedRelated {Γ Δ : List Ty} (M : Constructors I) (s : MarkedSubstitution Symbol arity Γ Δ) (hs : RangeConfined I s)
    (f : HeadIndex I) (τ : TypedExtraDownsets.TypeIndex I)
    (A : ArgumentActions I Γ (headArguments arity f.val)) (B : ArgumentActions I Δ (headArguments arity f.val))
    (types : List Ty) (ht : ∀ υ ∈ types,υ ∈ TypedExtraDownsets.types I)
    (E : ArgumentActions I Γ types) (F : ArgumentActions I Δ types)
    (hab : ArgumentsRelated M s hs A B) (hef : ArgumentsRelated M s hs E F) :
    Related M s hs (FunctionalSpineActionsProof.markedAction f τ A types ht E)
      (FunctionalSpineActionsProof.markedAction f τ B types ht F) := by
  intro P ρ η ha
  have hstate := markedStateEq M f A B types ht E F P ρ η (hab P ρ η ha) (hef P ρ η ha)
  have he := congrArg (M.val f τ P) hstate
  refine ⟨he,?_⟩
  intro sourceMask targetMask hc requested υ args h
  exact functionalScanEq f τ (markedEvaluate f τ A types ht E) (markedEvaluate f τ B types ht F)
    (markedState f A types ht E) (markedState f B types ht F) M P ρ η he hstate sourceMask targetMask requested υ args h

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualLimitSubstitutionSupportProof
