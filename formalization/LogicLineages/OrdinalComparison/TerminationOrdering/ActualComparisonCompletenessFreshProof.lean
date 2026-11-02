module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessSelectProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessFreshProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment FullListValueApplication CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration ActualComparisonCompleteness RenamingEquivariance FunctionalSpineActions OrdinaryFunctionalValue ActualComparisonCompletenessSupportProof ActualComparisonCompletenessOrdinaryProof ActualComparisonCompletenessSelectProof LambdaSpineActions LambdaObservationMatching

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem lambdaTarget {Γ : List Ty} {σ υ : Ty} (P : World I) (r : Renaming Γ (portTypes P.val++I.context))
    (t : MarkedTerm Symbol arity (σ::Γ) υ) (o : Obs I) (hp : o.ports=P.val)
    (he : renamePacked r ⟨.arrow σ υ,.lam t⟩=decode o hp) :
    ∃ b : Term Symbol arity (σ::(portTypes P.val++I.context)) υ,o=⟨P.val,.arrow σ υ,.lam b⟩ ∧ renameTerm t r.lift=embed b := by
  rcases o with ⟨ports,τ,body⟩
  dsimp at hp
  subst ports
  have ht := congrArg Sigma.fst he
  dsimp [renamePacked,decode] at ht
  subst τ
  have hb : MarkedTerm.lam (renameTerm t r.lift)=embed body := eq_of_heq (Sigma.mk.inj he).2
  cases body with
  | lam b => exact ⟨b,rfl,MarkedTerm.lam.inj hb⟩
  | var v => cases hb
  | app f a => cases hb
  | succC => cases hb
  | caseC => cases hb
  | recC => cases hb

theorem openingNamed {Γ : List Ty} (P : World I) (r : Renaming Γ (portTypes P.val++I.context))
    (σ υ : Ty) (i : Fin (budget I)) (h : MarkedFAbsTest.Opening I P σ υ i) :
    @Eq (Environment I (σ::Γ) ⟨(i,σ)::P.val,h.2.1⟩)
      (openingEnvironment (reindex r (identity I P)) σ υ i h)
      (reindex r.lift (identity I ⟨(i,σ)::P.val,h.2.1⟩)) := by
  funext τ v
  exact (congrArg (fun env : Environment I (σ::Γ) ⟨(i,σ)::P.val,h.2.1⟩ => env v)
    (StructuralRenamingSupportProof.openingReindex r (identity I P) σ υ i h)).symm.trans
    (congrArg (fun env : Environment I (σ::(portTypes P.val++I.context)) ⟨(i,σ)::P.val,h.2.1⟩ => env (r.lift v))
      (LiteralWorldTransportProof.openingIdentity Symbol inferInstance arity I P σ υ i h))

theorem lambdaRead {Γ : List Ty} {σ υ : Ty} (body : MarkedTerm Symbol arity (σ::Γ) υ)
    (A : OriginalSpineActions.PairedAction I (σ::Γ) υ) (M : Constructors I) (P : World I) (ρ : Environment I Γ P)
    (target : Term Symbol arity (σ::(portTypes P.val++I.context)) υ)
    (ho : (⟨P.val,.arrow σ υ,.lam target⟩ : Obs I) ∈ observations (budget I) I.target) :
    readBit false (LambdaSpineActionsProof.lambdaValue body A M P ρ) ⟨P.val,.arrow σ υ,.lam target⟩=
      matchTerm false (bodyEvaluator body A M) ρ (.lam target) := by
  let obs : ObservationAt I (.arrow σ υ) P := ⟨⟨P.val,.arrow σ υ,.lam target⟩,ho,rfl,rfl⟩
  rw [TypedObservationAccessProof.typedCoordinate Symbol inferInstance arity I (.arrow σ υ) P false _ ⟨P,fun _ hp => hp⟩ obs]
  simp only [coordinate,if_false,LambdaSpineActionsProof.valueLayer]
  change matchTerm false (bodyEvaluator body A M) (restrict (fun _ hp => hp) ρ) (.lam target)=_
  rw [TypedValueEnvironmentProof.restrictionIdentity Symbol inferInstance arity I Γ P ρ]

theorem absCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} {σ υ : Ty}
    (s t : MarkedTerm Symbol arity (σ::Γ) υ) (hm : Meaning (I := I) above false ⟨υ,s⟩ ⟨υ,t⟩) :
    Meaning (I := I) above false ⟨.arrow σ υ,.lam s⟩ ⟨.arrow σ υ,.lam t⟩ := by
  intro P r hs o ho hp he
  rcases lambdaTarget P r t o hp he with ⟨body,rfl,hbody⟩
  obtain ⟨i,hopen,hobs⟩ := LambdaObservationMatchingProof.genuineFreshOpening Symbol inferInstance arity I P σ υ body ho
  have hi := hm ⟨(i,σ)::P.val,hopen.2.1⟩ r.lift ⟨hs.1.2.2,hs.2⟩ ⟨(i,σ)::P.val,υ,body⟩ hobs rfl
    (congrArg (fun b : MarkedTerm Symbol arity (σ::(portTypes P.val++I.context)) υ => (⟨υ,b⟩ : RecursiveComparison.Packed Symbol arity _)) hbody)
  apply (lambdaRead s (buildTerm I s ⟨hs.1.2.2,hs.2⟩) (limit I above) P (reindex r (identity I P)) body ho).trans
  apply (LambdaObservationMatchingProof.literalMatch Symbol inferInstance arity I Γ σ υ s (bodyEvaluator s (buildTerm I s ⟨hs.1.2.2,hs.2⟩) (limit I above))
    P (reindex r (identity I P)) false body).mpr
  refine ⟨i,hopen,?_⟩
  exact (congrArg (fun env : Environment I (σ::Γ) ⟨(i,σ)::P.val,hopen.2.1⟩ =>
    readBit false (interpret ⟨s,⟨hs.1.2.2,hs.2⟩⟩ (limit I above) ⟨(i,σ)::P.val,hopen.2.1⟩ env) ⟨(i,σ)::P.val,υ,body⟩)
      (openingNamed P r σ υ i hopen)).trans hi

theorem openConfined {Γ : List Ty} (f : Head Symbol) (σ υ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (hf : f ∈ headList I)
    (hb : ArgumentsConfined I base) (hx : ArgumentsConfined I extras)
    (hσ : σ ∈ TypedExtraDownsets.types I) (hυ : υ ∈ TypedExtraDownsets.types I) :
    Confined I (openMarked f σ υ base extraTypes extras) := by
  have hbr := renameArgsConfined base hb (Renaming.weaken Γ σ)
  have hxr := renameArgsConfined extras hx (Renaming.weaken Γ σ)
  have hv : ArgumentsConfined I (.cons (.var (Variable.here : Variable (σ::Γ) σ)) .nil) := ⟨⟨hσ,trivial⟩,⟨trivial,trivial⟩⟩
  have he := InterpretedArgumentAppendProof.confinedAppend _ _ hxr hv
  exact ⟨⟨hυ,hbr.1,he.1⟩,⟨hf,hbr.2,he.2⟩⟩

theorem openValue {Γ : List Ty} (f : Head Symbol) (σ υ : Ty) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes) (hf : f ∈ headList I)
    (hb : ArgumentsConfined I base) (hx : ArgumentsConfined I extras)
    (hσ : σ ∈ TypedExtraDownsets.types I) (hυ : υ ∈ TypedExtraDownsets.types I)
    (M : Constructors I) (P : World I) (ρ : Environment I Γ P) (x : Value I σ P) :
    interpret ⟨openMarked f σ υ base extraTypes extras,openConfined f σ υ base extraTypes extras hf hb hx hσ hυ⟩ M P (extend x ρ)=
      M.val ⟨f,hf⟩ ⟨υ,hυ⟩ P (FunctionalTupleBuilder.appendInput
        (markedState ⟨f,hf⟩ (buildArguments I base hb) extraTypes (argumentTypeList extras hx) (buildArguments I extras hx) M P ρ)
        [⟨⟨σ,hσ⟩,x⟩]) := by
  let v : Arguments Symbol arity (σ::Γ) [σ] := .cons (.var .here) .nil
  have hv : ArgumentsConfined I v := ⟨⟨hσ,trivial⟩,⟨trivial,trivial⟩⟩
  have hxr := renameArgsConfined extras hx (Renaming.weaken Γ σ)
  have hp := InterpretedArgumentAppendProof.orderedPackedAppend Symbol inferInstance arity I (σ::Γ) extraTypes [σ]
    (renameArguments extras (Renaming.weaken Γ σ)) v hxr hv (InterpretedArgumentAppendProof.confinedAppend _ _ hxr hv) M P (extend x ρ)
  have he := renameArgsValues extras hx (Renaming.weaken Γ σ) M P (extend x ρ)
  have hpack : InterpretedArgumentAppend.packedValues (renameArguments extras (Renaming.weaken Γ σ)) hxr M P (extend x ρ)=
      InterpretedArgumentAppend.packedValues extras hx M P ρ := congrArg (packArguments extraTypes (argumentTypeList extras hx)) he
  have hpv : InterpretedArgumentAppend.packedValues v hv M P (extend x ρ)=[⟨⟨σ,hσ⟩,x⟩] := by
    simp only [v,InterpretedArgumentAppend.packedValues,packArguments,List.ofFn_succ,List.ofFn_zero]
    rfl
  apply congrArg (M.val ⟨f,hf⟩ ⟨υ,hυ⟩ P)
  apply Prod.ext
  · exact renameArgsValues base hb (Renaming.weaken Γ σ) M P (extend x ρ)
  · exact (congrArg (TypedExtraAppendProof.appendExtras (emptyExtras I P))
      (hp.trans (congrArg₂ List.append hpack hpv))).trans
      (InterpretedArgumentAppendProof.downclosureAppend Symbol inferInstance arity I P (emptyExtras I P) _ _).symm

theorem fAbsCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} {σ υ : Ty}
    (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes)
    (t : MarkedTerm Symbol arity (σ::Γ) υ)
    (hm : Meaning (I := I) above false ⟨υ,openMarked f σ υ base extraTypes extras⟩ ⟨υ,t⟩) :
    Meaning (I := I) above false ⟨.arrow σ υ,.marked f (.arrow σ υ) base extraTypes extras⟩ ⟨.arrow σ υ,.lam t⟩ := by
  intro P r hs o ho hp he
  rcases lambdaTarget P r t o hp he with ⟨body,rfl,hbody⟩
  obtain ⟨i,hopen,hobs⟩ := LambdaObservationMatchingProof.genuineFreshOpening Symbol inferInstance arity I P σ υ body ho
  let Q : World I := ⟨(i,σ)::P.val,hopen.2.1⟩
  let ext : Extends P Q := fun p hp => List.mem_cons_of_mem _ hp
  let ρ : Environment I Γ P := reindex r (identity I P)
  have hb : ArgumentsConfined I base := ⟨hs.1.2.1,hs.2.2.1⟩
  have hx : ArgumentsConfined I extras := ⟨hs.1.2.2,hs.2.2.2⟩
  let a := markedState ⟨f,hs.2.1⟩ (buildArguments I base hb) extraTypes (argumentTypeList extras hx) (buildArguments I extras hx) (limit I above) P ρ
  have hc := openConfined f σ υ base extraTypes extras hs.2.1 hb hx hopen.2.2.1 hopen.2.2.2
  have hi := hm Q r.lift hc ⟨Q.val,υ,body⟩ hobs rfl
    (congrArg (fun b : MarkedTerm Symbol arity (σ::(portTypes P.val++I.context)) υ => (⟨υ,b⟩ : RecursiveComparison.Packed Symbol arity _)) hbody)
  have hv := openValue f σ υ base extraTypes extras hs.2.1 hb hx hopen.2.2.1 hopen.2.2.2
    (limit I above) Q (restrict ext ρ) (LiteralVariableValueProof.variableValue (I := I) (P := Q) Variable.here)
  have hsR := FunctionalSpineActionsSupportProof.stateRestriction Symbol inferInstance arity I Γ ⟨f,hs.2.1⟩
    (buildArguments I base hb) extraTypes (argumentTypeList extras hx) (buildArguments I extras hx) (limit I above) P Q ext ρ
  have hi' : readBit false (interpret ⟨openMarked f σ υ base extraTypes extras,hc⟩ (limit I above) Q
      (openingEnvironment ρ σ υ i hopen)) ⟨Q.val,υ,body⟩=true :=
    (congrArg (fun env : Environment I (σ::Γ) Q => readBit false
      (interpret ⟨openMarked f σ υ base extraTypes extras,hc⟩ (limit I above) Q env) ⟨Q.val,υ,body⟩)
      (openingNamed P r σ υ i hopen)).trans hi
  have hopenRead : MarkedFAbsTest.openingRead (limit I above) ⟨f,hs.2.1⟩ a σ υ body i hopen=true := by
    have hv' := hv.trans (congrArg (fun state => (limit I above).val ⟨f,hs.2.1⟩ ⟨υ,hopen.2.2.2⟩ Q
      (FunctionalTupleBuilder.appendInput state [⟨⟨σ,hopen.2.2.1⟩,LiteralVariableValueProof.variableValue (I := I) (P := Q) Variable.here⟩])) hsR.symm)
    exact (congrArg (fun v : Value I υ Q => readBit false v ⟨Q.val,υ,body⟩) hv').symm.trans hi'
  have hfabs : MarkedFAbsTest.fAbsTest (limit I above) ⟨f,hs.2.1⟩ a ⟨P.val,.arrow σ υ,.lam body⟩=true :=
    (MarkedFAbsTestProof.literalLambdaEquation Symbol inferInstance arity I (limit I above) ⟨f,hs.2.1⟩ P σ υ body a).trans
      ((MarkedFAbsTestProof.lambdaCalibration Symbol inferInstance arity I (limit I above) ⟨f,hs.2.1⟩ P σ υ body a).mpr ⟨i,hopen,hopenRead⟩)
  apply markedRule above ⟨f,hs.2.1⟩ ⟨.arrow σ υ,hs.1.1⟩ P a _ ho rfl rfl
  simp only [hfabs,Bool.or_true]

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessFreshProof
