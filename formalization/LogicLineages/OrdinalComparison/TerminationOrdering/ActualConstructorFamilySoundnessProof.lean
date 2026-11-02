module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualConstructorFamilySoundnessTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualConstructorFamilySoundnessProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedExtraDownsets CoherentConstructorLattice RecursiveComparison ConstructorInputLogicalRelation ActualComparisonCompleteness ActualValueLogicalRelation CopyStatStageSoundness SourceConstructorIteration SourceConstructorOperator TypedObservationAccess

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem markedApplication {Γ : List Ty} (f : Head Symbol) (τ : Ty)
    (base : Arguments Symbol arity Γ (headArguments arity f)) (extraTypes : List Ty) (extras : Arguments Symbol arity Γ extraTypes)
    {types : List Ty} {υ : Ty} (args : Arguments Symbol arity Γ types) (h : τ=arrows types υ) (hn : types≠[]) :
    applyOriginalWith (.marked f τ base extraTypes extras) (fun v => .var v) args h=
      some (.marked f υ base (extraTypes++types) (appendArguments extras args)) := by
  cases args with
  | nil => exact False.elim (hn rfl)
  | cons a rest =>
    simp only [applyOriginalWith,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2 Symbol arity Γ _ base,
      Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2 Symbol arity Γ _ extras]

theorem currentBits (above : Symbol → Symbol → Prop) [DecidableRel above] (M : Constructors I) (f : HeadIndex I)
    (τ : TypeIndex I) (P : World I) (a : Inputs I f P) (o : ObservationAt I τ.val P) :
    readBit false ((SourceConstructorOperatorProof.operator above M).val f τ P a) o.val=
      (MarkedSelectTest.selectTest M f a o.val || MarkedCopyTest.copyTest above M f a o.val || MarkedStatTest.statTest M f a o.val || MarkedFAbsTest.fAbsTest M f a o.val) ∧
    readBit true ((SourceConstructorOperatorProof.operator above M).val f τ P a) o.val=false := by
  have H := (SourceConstructorOperatorProof.sourceBitEquations Symbol inferInstance arity I above inferInstance M f τ P a ⟨P,fun _ hp => hp⟩).2 o
  rw [(inputFamily I f).restrictIdentity P a] at H
  constructor
  · exact (TypedObservationAccessProof.typedCoordinate Symbol inferInstance arity I τ.val P false _ ⟨P,fun _ hp => hp⟩ o).trans H.1
  · exact (TypedObservationAccessProof.typedCoordinate Symbol inferInstance arity I τ.val P true _ ⟨P,fun _ hp => hp⟩ o).trans H.2

theorem operatorPreservation : ActualConstructorFamilySoundnessTargets.OperatorPreservation := by
  intro Symbol inst arity I above dec M hM f τ P a base types extras ha
  let N := SourceConstructorOperatorProof.operator above M
  rw [Related]
  constructor
  · intro Q h o
    let aQ := (inputFamily I f).restrict h a
    let bQ := renameArguments base (LogicalRelationWorlds.portRename h)
    let eQ := renameArguments extras (LogicalRelationWorlds.portRename h)
    have hi := ConstructorInputLogicalRelationProof.inputWeakening Symbol inst arity I above f P Q h a base types extras ha
    have he : weaken h (N.val f τ P a)=N.val f τ Q aQ := N.property.2 f τ P Q h a
    have hb := currentBits above M f τ Q aQ o
    constructor
    · intro ht
      rw [he,hb.1] at ht
      simp only [Bool.or_eq_true_iff] at ht
      rcases ht with ((hsel | hcopy) | hstat) | hfabs
      · exact SelectStageSoundnessProof.selectSound Symbol inst arity I above dec M f τ Q aQ bQ types eQ o hM hi hsel
      · exact CopyStatStageSoundnessProof.copySound Symbol inst arity I above dec M f τ Q aQ bQ types eQ o hM hi hcopy
      · exact CopyStatStageSoundnessProof.statSound Symbol inst arity I above dec M f τ Q aQ bQ types eQ o hM hi hstat
      · exact FAbsStageSoundnessProof.fAbsSound Symbol inst arity I above dec M f τ Q aQ bQ types eQ o hM hi hfabs
    · intro ht
      rw [he,hb.2] at ht
      cases ht
  · intro Q h s v args hv
    let aQ := (inputFamily I f).restrict h a
    let bQ := renameArguments base (LogicalRelationWorlds.portRename h)
    let eQ := renameArguments extras (LogicalRelationWorlds.portRename h)
    have hi := ConstructorInputLogicalRelationProof.inputWeakening Symbol inst arity I above f P Q h a base types extras ha
    have he : weaken h (N.val f τ P a)=N.val f τ Q aQ := N.property.2 f τ P Q h a
    have hs := (Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration τ.val s.val.1 s.val.2).mp s.property
    have hap := markedApplication f.val τ.val bQ types eQ args hs.2.symm hs.1
    have hsources : futureSyntax h (.marked f.val τ.val base types extras)=MarkedTerm.marked f.val τ.val bQ types eQ := by
      rfl
    have hap' : applyOriginalWith (futureSyntax h (.marked f.val τ.val base types extras)) (fun x => .var x) args hs.2.symm=
        some (.marked f.val s.val.2 bQ (types++s.val.1) (appendArguments eQ args)) :=
      (congrArg (fun q : SyntaxAt I τ.val Q => applyOriginalWith q (fun x => .var x) args hs.2.symm) hsources).trans hap
    have htypes : ∀ υ ∈ s.val.1,υ ∈ TypedExtraDownsets.types I := fun υ hυ =>
      FullTuplePacking.sourceTypeClosed I τ.property ((Source.SourceArrowSuffixesProof.arrowSuffixSubtypes τ.val _ _ s.property).2 υ hυ)
    have hin := ConstructorInputLogicalRelationProof.inputAppend Symbol inst arity I above f Q aQ bQ types eQ s.val.1 htypes v args hi hv
    have hr := hM f (FullTuplePacking.resultTag I τ s) Q
      (FunctionalTupleBuilder.appendInput aQ (FunctionalSpineActions.packArguments s.val.1 htypes v)) bQ (types++s.val.1) (appendArguments eQ args) hin
    have htable := SourceConstructorOperatorProof.fullTupleEquation Symbol inst arity I above dec M f τ Q aQ ⟨Q,fun _ hp => hp⟩ s v
    rw [(inputFamily I f).restrictIdentity Q aQ] at htable
    have hvEq : applyValue (weaken h (N.val f τ P a)) s v=
        M.val f (FullTuplePacking.resultTag I τ s) Q (FunctionalTupleBuilder.appendInput aQ (FullTuplePacking.packTuple τ s v)) :=
      (congrArg (fun value : Value I τ.val Q => applyValue value s v) he).trans htable
    have hr' : Related I above s.val.2 Q (applyValue (weaken h (N.val f τ P a)) s v)
        (.marked f.val s.val.2 bQ (types++s.val.1) (appendArguments eQ args)) :=
      Eq.mp (congrArg (fun value : Value I s.val.2 Q => Related I above s.val.2 Q value
        (.marked f.val s.val.2 bQ (types++s.val.1) (appendArguments eQ args))) hvEq.symm) hr
    split
    next hnone =>
      have impossible := hap'.symm.trans hnone
      cases impossible
    next result hresult =>
      have heq := Option.some.inj (hap'.symm.trans hresult)
      cases heq
      exact hr'

theorem actualIteratesSound : ActualConstructorFamilySoundnessTargets.ActualIteratesSound := by
  intro Symbol inst arity I above dec n
  induction n with
  | zero => exact ConstructorInputLogicalRelationProof.bottomFamilySound Symbol inst arity I above
  | succ n ih => exact operatorPreservation Symbol inst arity I above dec (iterate I above n) ih

theorem actualLimitSound : ActualConstructorFamilySoundnessTargets.ActualLimitSound := by
  intro Symbol inst arity I above dec
  exact actualIteratesSound Symbol inst arity I above dec (fuel I)

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualConstructorFamilySoundnessProof
