module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryLogicalRelationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryLogicalRelationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice RecursiveComparison ConstructorInputLogicalRelation ActualComparisonCompleteness ActualComparisonCompletenessSupportProof ActualValueLogicalRelation OrdinaryFunctionalValue SourceConstructorIteration TypedObservationAccess

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem ordinaryApplication {Γ : List Ty} (f : Head Symbol) (base : Arguments Symbol arity Γ (headArguments arity f))
    {types : List Ty} {τ : Ty} (args : Arguments Symbol arity Γ types) (h : headResult f=arrows types τ) (hn : types≠[]) :
    applyOriginalWith (.ordinary f base) (fun v => .var v) args h=some (.marked f τ base types args) := by
  cases args with
  | nil => exact False.elim (hn rfl)
  | cons a rest => simp only [applyOriginalWith,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2 Symbol arity Γ _ base]

theorem funSound (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (hb : ∀ i,Related I above ((headArguments arity f.val).get i) P (b i) (argumentAt base i))
    (o : ObservationAt I (headResult f.val) P) (htest : funMatch f b o.val=true) :
    Weak Symbol arity above (portTypes P.val++I.context) ⟨headResult f.val,.ordinary f.val base⟩ ⟨headResult f.val,observedTerm o⟩ := by
  rcases o with ⟨⟨ports,τ,body⟩,hom,hp,ht⟩
  dsimp at hp ht
  subst ports
  subst τ
  obtain ⟨g,args,hroot,heq,htype,hmatch⟩ := (OrdinaryFunctionalValueProof.funCalibration Symbol inferInstance arity I f P b _).mp htest
  have he := (OrdinaryObservationViewProof.rootCalibration Symbol arity _ _ body g args).mp hroot
  have ho := CopyStatStageSoundnessProof.childrenObserved P g args _ hom rfl he.symm
  have hv := CopyStatStageSoundnessProof.packedArgumentsRelated above P (headArguments arity f.val)
    (CoherentConstructorLatticeProof.headBaseTypes Symbol inferInstance arity I f) b base hb
  have ht := (FiniteOccurrenceMatchingProof.weakCalibration Symbol inferInstance arity I P (packBase f b) _).mpr hmatch
  obtain ⟨matched,hperm,hw⟩ := RelatedOccurrenceMatchingProof.weakSound Symbol inferInstance arity I above P _ _ _ _ hv ho ht
  exact he.symm ▸ Weak.fun_ f.val g base args matched heq htype hperm hw

theorem emptyInput (above : Symbol → Symbol → Prop) (f : HeadIndex I) (P : World I) (b : BaseTuple I f P)
    (base : Arguments Symbol arity (portTypes P.val++I.context) (headArguments arity f.val))
    (hb : ∀ i,Related I above ((headArguments arity f.val).get i) P (b i) (argumentAt base i)) :
    InputRelated I above f P ⟨b,emptyExtras I P⟩ base (.nil : Arguments Symbol arity _ []) := by
  refine ⟨hb,?_⟩
  intro p hp
  exact False.elim (Finset.notMem_empty p.2 hp)

theorem ordinaryRelated : OrdinaryLogicalRelationTargets.OrdinaryRelated := by
  intro Symbol inst arity I above dec M f P b base hM hb
  rw [Related]
  constructor
  · intro Q h o
    let bQ := weakenBase h b
    let baseQ := renameArguments base (LogicalRelationWorlds.portRename h)
    have hbase : ∀ i,Related I above ((headArguments arity f.val).get i) Q (bQ i) (argumentAt baseQ i) := by
      intro i
      rw [ConstructorInputLogicalRelationProof.argumentAtRename]
      exact LogicalRelationWorldsProof.relatedWeakening Symbol inst arity I above _ P Q h _ _ (hb i)
    obtain ⟨hr,heq⟩ := OrdinaryFunctionalValueProof.ordinaryBitEquations Symbol inst arity I M f P b
    have hm := hM f ⟨headResult f.val,hr⟩ Q ⟨bQ,emptyExtras I Q⟩ baseQ [] .nil (emptyInput above f Q bQ baseQ hbase)
    have hports : ∀ p ∈ Q.val,p ∈ o.val.ports := by rw [o.property.2.1]; exact fun _ hp => hp
    constructor
    · intro ht
      rw [TypedObservationAccessProof.restrictionAccess Symbol inst arity I _ P false Q h _ _ hports,
        TypedObservationAccessProof.typedCoordinate Symbol inst arity I _ P false _ ⟨Q,h⟩ o] at ht
      change ((layerView I _ P (ordinaryValue M f b)).val.1 ⟨Q,h⟩).2.1 o=true at ht
      rw [((heq ⟨Q,h⟩).2 o).1] at ht
      rcases Bool.or_eq_true_iff.mp ht with hfun | hmark
      · exact funSound above f Q bQ baseQ hbase o hfun
      · exact Weak.put f.val baseQ (observedTerm o) (SelectStageSoundnessProof.relatedWeakCurrent above _ _ hm o hmark)
    · intro ht
      rw [TypedObservationAccessProof.restrictionAccess Symbol inst arity I _ P true Q h _ _ hports,
        TypedObservationAccessProof.typedCoordinate Symbol inst arity I _ P true _ ⟨Q,h⟩ o] at ht
      change ((layerView I _ P (ordinaryValue M f b)).val.1 ⟨Q,h⟩).2.2 o=true at ht
      rw [((heq ⟨Q,h⟩).2 o).2] at ht
      exact Strict.mark (.ordinary f.val baseQ) (.marked f.val (headResult f.val) baseQ [] .nil) (observedTerm o) rfl
        (SelectStageSoundnessProof.relatedWeakCurrent above _ _ hm o ht)
  · intro Q h s values args hargs
    let bQ := weakenBase h b
    let baseQ := renameArguments base (LogicalRelationWorlds.portRename h)
    have hbase : ∀ i,Related I above ((headArguments arity f.val).get i) Q (bQ i) (argumentAt baseQ i) := by
      intro i
      rw [ConstructorInputLogicalRelationProof.argumentAtRename]
      exact LogicalRelationWorldsProof.relatedWeakening Symbol inst arity I above _ P Q h _ _ (hb i)
    obtain ⟨hr,htable⟩ := OrdinaryFunctionalValueProof.fullTupleEquation Symbol inst arity I M f P b
    have htypes : ∀ υ ∈ s.val.1,υ ∈ TypedExtraDownsets.types I := fun υ hυ =>
      FullTuplePacking.sourceTypeClosed I hr ((Source.SourceArrowSuffixesProof.arrowSuffixSubtypes _ _ _ s.property).2 υ hυ)
    have hin := ConstructorInputLogicalRelationProof.inputAppend Symbol inst arity I above f Q ⟨bQ,emptyExtras I Q⟩ baseQ [] .nil
      s.val.1 htypes values args (emptyInput above f Q bQ baseQ hbase) hargs
    have hrel := hM f (FullTuplePacking.resultTag I ⟨headResult f.val,hr⟩ s) Q
      (FunctionalTupleBuilder.appendInput ⟨bQ,emptyExtras I Q⟩ (FunctionalSpineActions.packArguments s.val.1 htypes values))
      baseQ s.val.1 args hin
    have hvEq : applyValue (weaken h (ordinaryValue M f b)) s values=
        M.val f (FullTuplePacking.resultTag I ⟨headResult f.val,hr⟩ s) Q
          ⟨bQ,TypedExtraAppendProof.appendExtras (emptyExtras I Q) (FullTuplePacking.packTuple ⟨headResult f.val,hr⟩ s values)⟩ := by
      unfold applyValue
      rw [RecursiveNaturalDomainsProof.layerViewWeaken]
      exact htable ⟨Q,h⟩ s values
    have hs := (Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration _ _ _).mp s.property
    have hsyntax : futureSyntax h (.ordinary f.val base)=MarkedTerm.ordinary f.val baseQ := rfl
    have hap := (congrArg (fun q : SyntaxAt I (headResult f.val) Q => applyOriginalWith q (fun v => .var v) args hs.2.symm) hsyntax).trans
      (ordinaryApplication f.val baseQ args hs.2.symm hs.1)
    have hr' : Related I above s.val.2 Q (applyValue (weaken h (ordinaryValue M f b)) s values)
        (.marked f.val s.val.2 baseQ s.val.1 args) :=
      Eq.mp (congrArg (fun v : Value I s.val.2 Q => Related I above s.val.2 Q v (.marked f.val s.val.2 baseQ s.val.1 args)) hvEq.symm) hrel
    split
    next hnone => cases hap.symm.trans hnone
    next result hresult =>
      have he := Option.some.inj (hap.symm.trans hresult)
      cases he
      exact hr'

theorem actualLimitOrdinaryRelated : OrdinaryLogicalRelationTargets.ActualLimitOrdinaryRelated := by
  intro Symbol inst arity I above dec f P b base hb
  exact ordinaryRelated Symbol inst arity I above dec (limit I above) f P b base
    (ActualConstructorFamilySoundnessProof.actualLimitSound Symbol inst arity I above dec) hb

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryLogicalRelationProof
