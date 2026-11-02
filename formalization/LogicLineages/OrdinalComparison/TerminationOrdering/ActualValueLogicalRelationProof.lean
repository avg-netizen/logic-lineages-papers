module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourcePortContexts Source.SourceOpenedObservations Source.SourceArrowSuffixes FiniteObservationBits NaturalTupleLayer RecursiveNaturalDomains TypedValueEnvironment TypedObservationAccess RecursiveComparison ActualComparisonCompleteness ActualValueLogicalRelation ExecutableDomainBottom

variable {Symbol : Type} [DecidableEq Symbol] {arity : Symbol → Nat} {I : Input Symbol arity}

theorem bitClause : ActualValueLogicalRelationTargets.BitClause := by
  intro Symbol inst arity I above τ P a q h
  exact (Related.eq_def I above τ P a q ▸ h).1

theorem fullTupleClause : ActualValueLogicalRelationTargets.FullTupleClause := by
  intro Symbol inst arity I above τ P a q h
  exact (Related.eq_def I above τ P a q ▸ h).2

theorem downward (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I)
    (a b : Value I τ P) (q : SyntaxAt I τ P) (hab : a ≤ b) (hr : Related I above τ P b q) :
    Related I above τ P a q := by
  rw [Related] at hr ⊢
  constructor
  · intro Q h o
    have hw := (family I τ).restrictMonotone P Q h a b hab
    exact ⟨fun ha => (hr.1 Q h o).1 (Bool.le_iff_imp.mp (TypedObservationAccessProof.readMonotone Symbol inferInstance arity I τ Q false _ _ o.val hw) ha),
      fun ha => (hr.1 Q h o).2 (Bool.le_iff_imp.mp (TypedObservationAccessProof.readMonotone Symbol inferInstance arity I τ Q true _ _ o.val hw) ha)⟩
  · intro Q h s v args hv
    have H := hr.2 Q h s v args hv
    have hle := MarkedSelectTestProof.fullApplicationMonotone (weaken h a) (weaken h b)
      ((family I τ).restrictMonotone P Q h a b hab) s v v le_rfl
    cases he : applyOriginalWith (futureSyntax h q) (fun x => .var x) args
      ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration τ _ _).mp s.property).2.symm with
    | none =>
      simp only [he] at H ⊢
      exact le_antisymm (H ▸ hle) (ExecutableDomainBottomProof.least Symbol inferInstance arity I s.val.2 Q _)
    | some result =>
      simp only [he] at H ⊢
      exact downward above s.val.2 Q _ _ result hle H
termination_by typeSize τ
decreasing_by exact (Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ _ _ s.property).1

theorem bottom (above : Symbol → Symbol → Prop) (τ : Ty) (P : World I) (q : SyntaxAt I τ P) :
    Related I above τ P (bottomValue I τ P) q := by
  rw [Related]
  constructor
  · intro Q h o
    have hw := ExecutableDomainBottomProof.weakeningBottom Symbol inferInstance arity I τ P Q h
    constructor
    · intro ht
      rw [hw,TypedObservationAccessProof.bottomFalse] at ht
      cases ht
    · intro ht
      rw [hw,TypedObservationAccessProof.bottomFalse] at ht
      cases ht
  · intro Q h s v args hv
    have hb : applyValue (weaken h (bottomValue I τ P)) s v=bottomValue I s.val.2 Q := by
      rw [ExecutableDomainBottomProof.weakeningBottom Symbol inferInstance arity I τ P Q h]
      exact ExecutableDomainBottomProof.allTablesBottom Symbol inferInstance arity I τ Q ⟨Q,fun _ hp => hp⟩ s v
    cases he : applyOriginalWith (futureSyntax h q) (fun x => .var x) args
      ((Source.SourceArrowSuffixesProof.exactArrowSuffixEnumeration τ _ _).mp s.property).2.symm with
    | none => exact hb
    | some result =>
      simp only [he,hb]
      exact bottom above s.val.2 Q result
termination_by typeSize τ
decreasing_by exact (Source.SourceArrowSuffixesProof.arrowSuffixStrictSize τ _ _ s.property).1

theorem downwardClosure : ActualValueLogicalRelationTargets.DownwardClosure := by
  intro Symbol inst arity I above τ P a b q hab hr
  exact downward above τ P a b q hab hr

theorem bottomRelated : ActualValueLogicalRelationTargets.BottomRelated := by
  intro Symbol inst arity I above τ P q
  exact bottom above τ P q

end LogicLineages.OrdinalComparison.TerminationOrdering.ActualValueLogicalRelationProof
