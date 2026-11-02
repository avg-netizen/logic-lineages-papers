module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValueTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValueProof
open Source Source.SourceMarkedSyntax Source.SourcePortContexts Source.SourceOpenedObservations FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice OrdinaryObservationView FiniteOccurrenceMatching TypedObservationAccess OrdinaryFunctionalValue

theorem groundHeadTransfer {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty}
    (K : Ty → Prop) (n : Nat) (f : Fin n → MarkedTerm Symbol arity Γ .ground)
    (ih : ∀ i,typesAllowed K (f i) → headsAllowed (fun g => K (headResult g)) (f i)) :
    argumentTypesAllowed K (groundArguments n f) → argumentsAllowed (fun g => K (headResult g)) (groundArguments n f) := by
  induction n with
  | zero => intro h; trivial
  | succ n hn =>
      intro h
      exact ⟨ih ⟨0,Nat.zero_lt_succ n⟩ h.1,hn (fun i => f i.succ) (fun i => ih i.succ) h.2⟩

theorem originalHeadResults {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (K : Ty → Prop) (t : Term Symbol arity Γ τ) :
    typesAllowed K (embed t) → headsAllowed (fun g => K (headResult g)) (embed t) := by
  induction t with
  | var v => intro h; trivial
  | lam body ih => intro h; exact ih h.2.2
  | app f a ihf iha =>
      intro h
      exact ⟨h.1,ihf h.2.1,iha h.2.2.1,True.intro⟩
  | zeroC => intro h; exact ⟨h.1,True.intro⟩
  | succC => intro h; exact ⟨h.1,True.intro⟩
  | caseC τ => intro h; exact ⟨h.1,True.intro⟩
  | recC τ => intro h; exact ⟨h.1,True.intro⟩
  | ranked s args ih =>
      intro h
      exact ⟨h.1,groundHeadTransfer K (arity s) (fun i => embed (args i)) ih h.2⟩

theorem sourceHeadResultTypes : OrdinaryFunctionalValueTargets.SourceHeadResultTypes := by
  intro Symbol inst arity I f
  have ht := (FiniteQueryPrimitivesProof.initialFrame Symbol arity I.context I.sourceType I.targetType I.source I.target).2.1
  have hh := originalHeadResults (fun τ => τ ∈ types I) I.source ht
  exact (FiniteQueryPrimitivesProof.literalHeadCalibration Symbol arity I.context I.sourceType (embed I.source)
    (fun g => headResult g ∈ types I)).mp hh f.val f.property

theorem basePackingCalibration : OrdinaryFunctionalValueTargets.BasePackingCalibration := by
  intro Symbol inst arity I f P b
  constructor
  · simp only [packBase,List.length_ofFn]
  · intro i; simp [packBase]

theorem funCalibration : OrdinaryFunctionalValueTargets.FunCalibration := by
  intro Symbol inst arity I f P b o
  cases hv : rootView o.body with
  | none => simp [funMatch,hv]
  | some data =>
      rcases data with ⟨g,args⟩
      simp only [funMatch,hv,Bool.and_eq_true_iff,decide_eq_true_eq]
      rw [FiniteOccurrenceMatchingProof.weakCalibration Symbol inst arity I P (packBase f b) (plainChildren o)]
      constructor
      · rintro ⟨⟨hh,hr⟩,hm⟩
        exact ⟨g,args,rfl,hh,hr,hm⟩
      · rintro ⟨g',args',he,hh,hr,hm⟩
        have he' : (⟨g,args⟩ : RootData Symbol arity (portTypes o.ports++I.context))=⟨g',args'⟩ := Option.some.inj he
        cases he'
        exact ⟨⟨hh,hr⟩,hm⟩

theorem emptyRestriction {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    {P Q : World I} (h : Extends P Q) : (TypedExtraDownsetsProof.extrasFamily I).restrict h (emptyExtras I P)=emptyExtras I Q := by
  funext τ
  apply Subtype.ext
  apply Finset.ext
  intro a
  simp only [TypedExtraDownsetsProof.extrasFamily,emptyExtras,TypedExtraDownsetsProof.imageMembership,Finset.notMem_empty,false_and,exists_false]

theorem ordinaryLayer {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}
    (M : Constructors I) (f : HeadIndex I) {P : World I} (b : BaseTuple I f P) (hr : headResult f.val ∈ types I) :
    (layerView I (headResult f.val) P (ordinaryValue M f b)).val=
      FunctionalTupleBuilder.buildRaw M f ⟨headResult f.val,hr⟩ (ordinaryBits M f hr b) ⟨b,emptyExtras I P⟩ := by
  simp only [ordinaryValue,dif_pos hr,FunctionalTupleBuilderProof.buildValue,RecursiveNaturalDomainsProof.layerViewFold]

theorem ordinaryBitEquations : OrdinaryFunctionalValueTargets.OrdinaryBitEquations := by
  intro Symbol inst arity I M f P b
  let hr := sourceHeadResultTypes Symbol inst arity I f
  refine ⟨hr,?_⟩
  intro Q
  rw [ordinaryLayer M f b hr]
  exact ⟨rfl,fun _ => ⟨rfl,rfl⟩⟩

theorem fullTupleEquation : OrdinaryFunctionalValueTargets.FullTupleEquation := by
  intro Symbol inst arity I M f P b
  let hr := sourceHeadResultTypes Symbol inst arity I f
  refine ⟨hr,?_⟩
  intro Q s v
  rw [ordinaryLayer M f b hr]
  change M.val f _ Q.val (FunctionalTupleBuilder.appendInput ((inputFamily I f).restrict Q.property ⟨b,emptyExtras I P⟩) _) = _
  simp only [inputFamily,FunctionalTupleBuilder.appendInput]
  rw [emptyRestriction]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryFunctionalValueProof
