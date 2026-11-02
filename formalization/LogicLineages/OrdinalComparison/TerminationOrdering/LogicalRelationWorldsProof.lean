module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment TypedObservationAccess RecursiveComparison ActualComparisonCompleteness ActualValueLogicalRelation LogicalRelationWorlds LiteralVariableValue

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem portRenameIdentity : LogicalRelationWorldsTargets.PortRenameIdentity := by
  intro Symbol inst arity I P τ v
  apply LiteralVariableValueProof.nameInjective (budget I) I.context P.val
    ((FiniteObservationBitsProof.worldCalibration Symbol arity I P.val).mp P.property).1 τ
  exact LiteralVariableValueProof.nameExtension (budget I) I.context P.val P.val (fun _ hp => hp) τ v

theorem portRenameComposition : LogicalRelationWorldsTargets.PortRenameComposition := by
  intro Symbol inst arity I P Q R h k τ v
  apply LiteralVariableValueProof.nameInjective (budget I) I.context R.val
    ((FiniteObservationBitsProof.worldCalibration Symbol arity I R.val).mp R.property).1 τ
  exact (LiteralVariableValueProof.nameExtension (budget I) I.context Q.val R.val k τ (portRename h v)).trans
    ((LiteralVariableValueProof.nameExtension (budget I) I.context P.val Q.val h τ v).trans
      (LiteralVariableValueProof.nameExtension (budget I) I.context P.val R.val (fun p hp => k p (h p hp)) τ v).symm)

theorem syntaxComposition {τ : Ty} {P Q R : World I} (h : Extends P Q) (k : Extends Q R) (q : SyntaxAt I τ P) :
    futureSyntax k (futureSyntax h q)=futureSyntax (fun p hp => k p (h p hp)) q := by
  have hr : @Eq (Renaming (portTypes P.val++I.context) (portTypes R.val++I.context))
      (fun {_} v => portRename k (portRename h v)) (portRename (fun p hp => k p (h p hp))) := by
    funext υ v
    exact portRenameComposition Symbol inferInstance arity I P Q R h k υ v
  exact (RenamingEquivarianceBindingProof.renameComposition q _ _ (portRename h) (portRename k)).trans
    (congrArg (fun r : Renaming (portTypes P.val++I.context) (portTypes R.val++I.context) => renameTerm q r) hr)

theorem relatedWeakening : LogicalRelationWorldsTargets.RelatedWeakening := by
  intro Symbol inst arity I above τ P Q h a q ha
  rw [Related] at ha ⊢
  constructor
  · intro R k o
    have hv : weaken k (weaken h a)=weaken (fun p hp => k p (h p hp)) a := (family I τ).restrictComposition P Q R h k a
    have hs := syntaxComposition h k q
    simpa only [←hv,←hs] using ha.1 R (fun p hp => k p (h p hp)) o
  · intro R k s v args hv
    have H := ha.2 R (fun p hp => k p (h p hp)) s v args hv
    have hw : weaken k (weaken h a)=weaken (fun p hp => k p (h p hp)) a := (family I τ).restrictComposition P Q R h k a
    have hs := syntaxComposition h k q
    simpa only [←hw,←hs] using H

theorem variableWeaken {τ : Ty} {P Q : World I} (h : Extends P Q) (v : Variable (portTypes P.val++I.context) τ) :
    weaken h (LiteralVariableValueProof.variableValue (I := I) v)=LiteralVariableValueProof.variableValue (portRename h v) := by
  apply RecursiveNaturalDomainsProof.layerViewInjective I τ Q
  rw [RecursiveNaturalDomainsProof.layerViewWeaken]
  simp only [LiteralVariableValueProof.variableValue,RecursiveNaturalDomainsProof.layerViewFold]
  apply Subtype.ext
  exact LiteralVariableValueProof.variableWeakening Symbol inferInstance arity I τ P Q h v

theorem variableNone {Γ : List Ty} {τ : Ty} (v : Variable Γ τ) {types : List Ty} {υ : Ty}
    (args : Arguments Symbol arity Γ types) (h : τ=arrows types υ) (hn : types≠[]) :
    applyOriginalWith (.var v) (fun x => .var x) args h=none := by
  cases args with
  | nil => exact False.elim (hn rfl)
  | cons a rest => rfl

theorem literalVariableRelated : LogicalRelationWorldsTargets.LiteralVariableRelated := by
  intro Symbol inst arity I above τ P v
  rw [Related]
  constructor
  · intro Q h o
    rw [variableWeaken]
    constructor
    · intro hb
      rw [TypedObservationAccessProof.typedCoordinate Symbol inst arity I τ Q false _ ⟨Q,fun _ hp => hp⟩ o] at hb
      simp only [coordinate,LiteralVariableValueProof.variableValue,RecursiveNaturalDomainsProof.layerViewFold] at hb
      have he := (LiteralVariableValueProof.literalVariableEquality Symbol inst arity I τ Q (portRename h v) ⟨Q,fun _ hp => hp⟩ o).mp hb
      have hi := portRenameIdentity Symbol inst arity I Q τ (portRename h v)
      change extendVariables I.context Q.val Q.val (fun _ hp => hp) (portRename h v)=portRename h v at hi
      rw [hi] at he
      let o' : ObservationAt I τ Q := ⟨⟨Q.val,τ,.var (portRename h v)⟩,by rw [←he]; exact o.property.1,rfl,rfl⟩
      have he' : o=o' := Subtype.ext he
      rw [he']
      exact Weak.var (portRename h v)
    · intro hb
      rw [TypedObservationAccessProof.typedCoordinate Symbol inst arity I τ Q true _ ⟨Q,fun _ hp => hp⟩ o] at hb
      simp only [coordinate,LiteralVariableValueProof.variableValue,RecursiveNaturalDomainsProof.layerViewFold] at hb
      have hf := (LiteralVariableValueProof.availabilityAndStrict Symbol inst arity I τ Q (portRename h v) ⟨Q,fun _ hp => hp⟩).2 o
      exact Bool.noConfusion (hf.symm.trans hb)
  · intro Q h s values args hargs
    have hne := ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration τ _ _).mp s.property).1
    have hn : applyOriginalWith (futureSyntax h (.var v)) (fun x => .var x) args
        ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration τ _ _).mp s.property).2.symm=none :=
      variableNone (portRename h v) args _ hne
    simp only [hn]
    rw [variableWeaken]
    unfold applyValue LiteralVariableValueProof.variableValue
    rw [RecursiveNaturalDomainsProof.layerViewFold]
    rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.LogicalRelationWorldsProof
