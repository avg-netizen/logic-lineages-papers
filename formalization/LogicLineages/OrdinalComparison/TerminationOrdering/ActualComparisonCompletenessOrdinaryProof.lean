module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessMatchingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessOrdinaryProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment CoherentConstructorLattice ConfinedStructuralInterpretation TypedObservationAccess RecursiveComparison SourceConstructorIteration ActualComparisonCompleteness RenamingEquivariance FunctionalSpineActions OrdinaryObservationView OrdinaryFunctionalValue ActualComparisonCompletenessSupportProof ActualComparisonCompletenessMatchingProof

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem forall₂OfMaps {α β γ : Type} {f : α → γ} {g : β → γ} {R : α → β → Prop}
    (xs : List α) (ys : List β) (he : xs.map f=ys.map g)
    (h : ∀ x ∈ xs,∀ y ∈ ys,f x=g y → R x y) : List.Forall₂ R xs ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => exact .nil
    | cons y ys => simp at he
  | cons x xs ih =>
    cases ys with
    | nil => simp at he
    | cons y ys =>
      have hp := List.cons.inj he
      exact .cons (h x List.mem_cons_self y List.mem_cons_self hp.1)
        (ih ys hp.2 (fun x hx y hy he => h x (List.mem_cons_of_mem _ hx) y (List.mem_cons_of_mem _ hy) he))

theorem targetArguments {Γ : List Ty} (P : World I) (r : Renaming Γ (portTypes P.val++I.context))
    (g : Head Symbol) (args : Arguments Symbol arity Γ (headArguments arity g)) (o : Obs I)
    (ho : o ∈ observations (budget I) I.target) (hp : o.ports=P.val)
    (he : renamePacked r ⟨headResult g,.ordinary g args⟩=decode o hp) :
    List.Forall₂ (TargetMatch P r) (argumentList args) (plainChildren o) := by
  rcases o with ⟨ports,τ,body⟩
  dsimp at hp
  subst ports
  have hv := (OrdinaryObservationViewProof.rootCalibration Symbol arity _ τ body g (renameArguments args r)).mpr he.symm
  have hm := OrdinaryObservationViewProof.argumentCalibration Symbol arity _ τ body g (renameArguments args r) hv
  rw [RenamingEquivarianceProof.argumentListRename] at hm
  rw [← OrdinaryObservationViewProof.plainChildrenCalibration Symbol arity I.context (budget I) ⟨P.val,τ,body⟩]
  apply List.forall₂_map_right_iff.mpr
  apply forall₂OfMaps (argumentList args) (childTerms body) hm.symm
  intro t ht c hc hec
  have hco := OrdinaryObservationViewProof.childProvenance Symbol arity I ⟨P.val,τ,body⟩ (observeChild P.val c) ho
    (List.mem_map.mpr ⟨c,hc,rfl⟩)
  exact ⟨hco.1,rfl,hec⟩

theorem baseMatch {Γ : List Ty} (M : Constructors I) (P : World I) (ρ : Environment I Γ P)
    (f : HeadIndex I) (base : Arguments Symbol arity Γ (headArguments arity f.val)) (hb : ArgumentsConfined I base) :
    List.Forall₂ (SourceMatch M P ρ) (argumentList base)
      (packBase f (evaluateArguments (buildArguments I base hb) M P ρ)) := by
  exact argumentsMatch base hb M P ρ

theorem ordinaryWeak (M : Constructors I) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P)
    (o : Obs I) (ho : o ∈ observations (budget I) I.target) (hp : o.ports=P.val)
    (ht : o.resultType=headResult f.val) (h : funMatch f b o=true ∨
      readBit false (M.val f ⟨headResult f.val,OrdinaryFunctionalValueProof.sourceHeadResultTypes Symbol inferInstance arity I f⟩ P ⟨b,emptyExtras I P⟩) o=true) :
    readBit false (ordinaryValue M f b) o=true := by
  let obs : ObservationAt I (headResult f.val) P := ⟨o,ho,hp,ht⟩
  obtain ⟨hr,hh⟩ := OrdinaryFunctionalValueProof.ordinaryBitEquations Symbol inferInstance arity I M f P b
  have hb : weakenBase (fun _ hp => hp) b=b := by
    funext i
    exact (family I _).restrictIdentity P (b i)
  have hw := ((hh ⟨P,fun _ hp => hp⟩).2 obs).1
  rw [hb] at hw
  have hor : (funMatch f b o || readBit false (M.val f ⟨headResult f.val,hr⟩ P ⟨b,emptyExtras I P⟩) o)=true := by
    exact Bool.or_eq_true_iff.mpr h
  exact (TypedObservationAccessProof.typedCoordinate Symbol inferInstance arity I (headResult f.val) P false _ ⟨P,fun _ hp => hp⟩ obs).trans (hw.trans hor)

theorem markedRule (above : Symbol → Symbol → Prop) [DecidableRel above] (f : HeadIndex I)
    (τ : TypedExtraDownsets.TypeIndex I) (P : World I) (a : Inputs I f P) (o : Obs I)
    (ho : o ∈ observations (budget I) I.target) (hp : o.ports=P.val) (ht : o.resultType=τ.val)
    (hh : (MarkedSelectTest.selectTest (limit I above) f a o || MarkedCopyTest.copyTest above (limit I above) f a o ||
      MarkedStatTest.statTest (limit I above) f a o || MarkedFAbsTest.fAbsTest (limit I above) f a o)=true) :
    readBit false ((limit I above).val f τ P a) o=true := by
  let obs : ObservationAt I τ.val P := ⟨o,ho,hp,ht⟩
  have hw := ((ActualLimitInterpretationProof.sourceBitEquations Symbol inferInstance arity I above inferInstance f τ P a ⟨P,fun _ hp => hp⟩).2 obs).1
  have hi := (inputFamily I f).restrictIdentity P a
  rw [hi] at hw
  exact (TypedObservationAccessProof.typedCoordinate Symbol inferInstance arity I τ.val P false _ ⟨P,fun _ hp => hp⟩ obs).trans (hw.trans hh)

theorem varCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty} {σ : Ty} (v : Variable Γ σ) :
    Meaning (I := I) above false ⟨σ,.var v⟩ ⟨σ,.var v⟩ := by
  intro P r hs o ho hp he
  rcases o with ⟨ports,τ,body⟩
  dsimp at hp
  subst ports
  have ht := congrArg Sigma.fst he
  dsimp [renamePacked,decode] at ht
  subst τ
  have hb : MarkedTerm.var (r v)=embed body := eq_of_heq (Sigma.mk.inj he).2
  cases body <;> try cases hb
  have ha : Accepted I σ P ⟨P.val,σ,.var (r v)⟩ := ⟨P.property,fun _ hp => hp,rfl,ho⟩
  simp [interpret,action,buildTerm,OriginalSpineActionsProof.variableAction,OriginalSpineActions.variableEvaluate,
      reindex,identity,readBit,ha,acceptedCoordinate,coordinate,LiteralVariableValueProof.variableValue,
      RecursiveNaturalDomainsProof.layerViewFold,LiteralVariableValue.variableRaw,LiteralVariableValue.variableBits,LiteralVariableValue.observationName]

theorem funCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    (f g : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f))
    (ts : Arguments Symbol arity Γ (headArguments arity g)) (matched : List (RecursiveComparison.Packed Symbol arity Γ))
    (hfg : headEquivalent f g) (htype : headResult f=headResult g) (hperm : (argumentList ts).Perm matched)
    (hm : List.Forall₂ (Meaning (I := I) above false) (argumentList ss) matched) :
    Meaning (I := I) above false ⟨headResult f,.ordinary f ss⟩ ⟨headResult g,.ordinary g ts⟩ := by
  intro P r hs o ho hp he
  have ht : o.resultType=headResult f := ((congrArg Sigma.fst he).symm.trans htype.symm)
  have htest := weakTruth above hperm hm P r (baseMatch (limit I above) P (reindex r (identity I P)) ⟨f,hs.2.1⟩ ss ⟨hs.1.2,hs.2.2⟩)
    (targetArguments P r g ts o ho hp he)
  apply ordinaryWeak (limit I above) ⟨f,hs.2.1⟩ P _ o ho hp ht
  apply Or.inl
  rcases o with ⟨ports,τ,body⟩
  dsimp at hp
  subst ports
  apply (OrdinaryFunctionalValueProof.funCalibration Symbol inferInstance arity I ⟨f,hs.2.1⟩ P _ ⟨P.val,τ,body⟩).mpr
  have hv := (OrdinaryObservationViewProof.rootCalibration Symbol arity _ τ body g (renameArguments ts r)).mpr he.symm
  rcases (FiniteOccurrenceMatchingProof.weakCalibration Symbol inferInstance arity I P _ _).mp htest with ⟨os,hop,hpair⟩
  exact ⟨g,renameArguments ts r,hv,hfg,htype,os,hop,hpair⟩

theorem putCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    (f : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f)) (t : MarkedTerm Symbol arity Γ (headResult f))
    (hm : Meaning (I := I) above false ⟨headResult f,.marked f (headResult f) ss [] .nil⟩ ⟨headResult f,t⟩) :
    Meaning (I := I) above false ⟨headResult f,.ordinary f ss⟩ ⟨headResult f,t⟩ := by
  intro P r hs o ho hp he
  have hmark := hm P r ⟨⟨hs.1.1,hs.1.2,trivial⟩,⟨hs.2.1,hs.2.2,trivial⟩⟩ o ho hp he
  have ht : o.resultType=headResult f := (congrArg Sigma.fst he).symm
  apply ordinaryWeak (limit I above) ⟨f,hs.2.1⟩ P _ o ho hp ht
  apply Or.inr
  simpa only [interpret,action,buildTerm,FunctionalSpineActionsProof.markedAction,FunctionalSpineActionsProof.assembleAction,
    markedEvaluate,markedState,packArguments,List.ofFn_zero,ActualStrictMarkSupportProof.emptyAppend] using hmark

theorem allChildren (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    (f g : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Γ extraTypes) (ts : Arguments Symbol arity Γ (headArguments arity g))
    (hf : f ∈ headList I) (hb : ArgumentsConfined I ss) (hx : ArgumentsConfined I extras)
    (hm : ∀ p ∈ argumentList ts,Meaning (I := I) above false ⟨p.1,.marked f p.1 ss extraTypes extras⟩ p)
    (P : World I) (r : Renaming Γ (portTypes P.val++I.context)) (o : Obs I)
    (ho : o ∈ observations (budget I) I.target) (hp : o.ports=P.val)
    (he : renamePacked r ⟨headResult g,.ordinary g ts⟩=decode o hp) :
    ∀ c ∈ plainChildren o,∃ ht : c.resultType ∈ TypedExtraDownsets.types I,
      readBit false ((limit I above).val ⟨f,hf⟩ ⟨c.resultType,ht⟩ P
        (markedState ⟨f,hf⟩ (buildArguments I ss hb) extraTypes (argumentTypeList extras hx)
          (buildArguments I extras hx) (limit I above) P (reindex r (identity I P)))) c=true := by
  intro c hc
  rcases rightWitness (targetArguments P r g ts o ho hp he) hc with ⟨p,hpm,hpt⟩
  rcases hpt with ⟨hcm,hcp,hce⟩
  have hct := MarkedCopyTestProof.genuineChildGuards Symbol inferInstance arity I o ho c hc
  have htype := congrArg Sigma.fst hce
  rcases p with ⟨σ,q⟩
  dsimp [renamePacked,decode] at htype
  have hσ : σ ∈ TypedExtraDownsets.types I := htype.symm ▸ hct
  have hi := hm ⟨σ,q⟩ hpm P r ⟨⟨hσ,hb.1,hx.1⟩,⟨hf,hb.2,hx.2⟩⟩ c hcm hcp hce
  refine ⟨hct,?_⟩
  cases htype
  exact hi

theorem copyCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    (f g : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Γ extraTypes) (ts : Arguments Symbol arity Γ (headArguments arity g))
    (hfg : headAbove above f g)
    (hm : ∀ p ∈ argumentList ts,Meaning (I := I) above false ⟨p.1,.marked f p.1 ss extraTypes extras⟩ p) :
    Meaning (I := I) above false ⟨headResult g,.marked f (headResult g) ss extraTypes extras⟩ ⟨headResult g,.ordinary g ts⟩ := by
  intro P r hs o ho hp he
  have hc := allChildren above f g ss extraTypes extras ts hs.2.1 ⟨hs.1.2.1,hs.2.2.1⟩ ⟨hs.1.2.2,hs.2.2.2⟩ hm P r o ho hp he
  have ht : o.resultType=headResult g := (congrArg Sigma.fst he).symm
  apply markedRule above ⟨f,hs.2.1⟩ ⟨headResult g,hs.1.1⟩ P _ o ho hp ht
  have hcTest : MarkedCopyTest.copyTest above (limit I above) ⟨f,hs.2.1⟩
      (markedState ⟨f,hs.2.1⟩ (buildArguments I ss ⟨hs.1.2.1,hs.2.2.1⟩) extraTypes
        (argumentTypeList extras ⟨hs.1.2.2,hs.2.2.2⟩) (buildArguments I extras ⟨hs.1.2.2,hs.2.2.2⟩)
        (limit I above) P (reindex r (identity I P))) o=true := by
    rcases o with ⟨ports,τ,body⟩
    dsimp at hp
    subst ports
    apply (MarkedCopyTestProof.copyCalibration Symbol inferInstance arity I above inferInstance (limit I above) ⟨f,hs.2.1⟩ P _ _).mpr
    exact ⟨g,renameArguments ts r,(OrdinaryObservationViewProof.rootCalibration Symbol arity _ τ body g (renameArguments ts r)).mpr he.symm,hfg,hc⟩
  simp only [hcTest,Bool.or_true,Bool.true_or]

theorem statCase (above : Symbol → Symbol → Prop) [DecidableRel above] {Γ : List Ty}
    (f g : Head Symbol) (ss : Arguments Symbol arity Γ (headArguments arity f)) (extraTypes : List Ty)
    (extras : Arguments Symbol arity Γ extraTypes) (ts : Arguments Symbol arity Γ (headArguments arity g))
    (hfg : headEquivalent f g) (hstrict : MultiMeaning (I := I) above (argumentList ss) (argumentList ts))
    (hm : ∀ p ∈ argumentList ts,Meaning (I := I) above false ⟨p.1,.marked f p.1 ss extraTypes extras⟩ p) :
    Meaning (I := I) above false ⟨headResult g,.marked f (headResult g) ss extraTypes extras⟩ ⟨headResult g,.ordinary g ts⟩ := by
  intro P r hs o ho hp he
  have hc := allChildren above f g ss extraTypes extras ts hs.2.1 ⟨hs.1.2.1,hs.2.2.1⟩ ⟨hs.1.2.2,hs.2.2.2⟩ hm P r o ho hp he
  have ht : o.resultType=headResult g := (congrArg Sigma.fst he).symm
  have hst := strictTruth above hstrict P r
    (baseMatch (limit I above) P (reindex r (identity I P)) ⟨f,hs.2.1⟩ ss ⟨hs.1.2.1,hs.2.2.1⟩)
    (targetArguments P r g ts o ho hp he)
  apply markedRule above ⟨f,hs.2.1⟩ ⟨headResult g,hs.1.1⟩ P _ o ho hp ht
  have hsTest : MarkedStatTest.statTest (limit I above) ⟨f,hs.2.1⟩
      (markedState ⟨f,hs.2.1⟩ (buildArguments I ss ⟨hs.1.2.1,hs.2.2.1⟩) extraTypes
        (argumentTypeList extras ⟨hs.1.2.2,hs.2.2.2⟩) (buildArguments I extras ⟨hs.1.2.2,hs.2.2.2⟩)
        (limit I above) P (reindex r (identity I P))) o=true := by
    rcases o with ⟨ports,τ,body⟩
    dsimp at hp
    subst ports
    apply (MarkedStatTestProof.statCalibration Symbol inferInstance arity I (limit I above) ⟨f,hs.2.1⟩ P _ _).mpr
    exact ⟨g,renameArguments ts r,(OrdinaryObservationViewProof.rootCalibration Symbol arity _ τ body g (renameArguments ts r)).mpr he.symm,hfg,
      (FiniteOccurrenceMatchingProof.strictCalibration Symbol inferInstance arity I P _ _).mp hst,hc⟩
  simp only [hsTest,Bool.or_true,Bool.true_or]

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualComparisonCompletenessOrdinaryProof
