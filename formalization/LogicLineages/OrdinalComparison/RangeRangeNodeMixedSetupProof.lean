module
public import LogicLineages.OrdinalComparison.RangeRangeNodeQueryProof
public import LogicLineages.OrdinalComparison.RangeRangeNodeLimitFixedProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

/-- The actual source query can put the larger outer exponent on either side.
Recursive mixed children always retain their canonical high-first orientation. -/
def MixedOrientations (q : ComparisonQuery) (H L : OneVariableComparisonExpr) : Prop :=
  q.1=(oneVariableComparisonEncode H,oneVariableComparisonEncode L) ∨
    q.1=(oneVariableComparisonEncode L,oneVariableComparisonEncode H)

theorem mixed_normalization (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (hlt : lower.1.repr<eta.1.repr) :
    encodedRangeRangeNormalization q.1=
      encodedSuccessorNormalization (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode lower.1) c := by
  have hgt := (rawComparisonOrdinalCorrect eta lower).2.2.mpr hlt
  have hngt : rawComparisonCode (rawNoteEncode lower.1) (rawNoteEncode eta.1)≠2 := by
    intro h
    exact (lt_asymm hlt) ((rawComparisonOrdinalCorrect lower eta).2.2.mp h)
  rcases hq with hq | hq
  · simp only [encodedRangeRangeNormalization,hq,ComparisonExpansion.outer_source,
      hgt,if_true,ComparisonExpansion.prefix_program.2]
  · simp only [encodedRangeRangeNormalization,hq,ComparisonExpansion.outer_source,
      hngt,if_false,ComparisonExpansion.prefix_program.2]

theorem mixed_children (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (hlt : lower.1.repr<eta.1.repr) :
    encodedComparisonChildren q.1.1 q.1.2=
      encodedComparisonMixedChildren (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))
        (oneVariableComparisonEncode (.range (v++[(lower,d)]) F)) := by
  have hgt := (rawComparisonOrdinalCorrect eta lower).2.2.mpr hlt
  have hngt : rawComparisonCode (rawNoteEncode lower.1) (rawNoteEncode eta.1)≠2 := by
    intro h
    exact (lt_asymm hlt) ((rawComparisonOrdinalCorrect lower eta).2.2.mp h)
  have hne : rawNoteEncode eta.1≠rawNoteEncode lower.1 := by
    intro heq
    have hh := congrArg rawNoteDecode heq
    rw [rawNoteDecodeEncode eta.1,rawNoteDecodeEncode lower.1] at hh
    exact (ne_of_gt hlt) (congrArg ONote.repr hh)
  have hmodR : oneVariableComparisonEncode (.range (w++[(eta,c)]) E)%2=1 := by
    change (2*Nat.pair _ _+1)%2=1
    omega
  have hmodS : oneVariableComparisonEncode (.range (v++[(lower,d)]) F)%2=1 := by
    change (2*Nat.pair _ _+1)%2=1
    omega
  rcases hq with hq | hq
  · simp only [hq,encodedComparisonChildren,ComparisonSourceDomain.correct _ hR,
      ComparisonSourceDomain.correct _ hS,ne_eq,not_true_eq_false,or_self,if_false,
      hmodR,hmodS,Nat.one_ne_zero,ComparisonExpansion.outer_source,hne,hgt,if_true]
  · simp only [hq,encodedComparisonChildren,ComparisonSourceDomain.correct _ hR,
      ComparisonSourceDomain.correct _ hS,ne_eq,not_true_eq_false,or_self,if_false,
      hmodR,hmodS,Nat.one_ne_zero,ComparisonExpansion.outer_source,Ne.symm hne,hngt]

theorem mixed_lower_context (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F)) :
    positiveExprEncode (.head (comparisonPrincipalNote lower) .input)∈encodedComparisonQueryContexts q.1 := by
  rcases hq with hq | hq
  · rw [encodedComparisonQueryContexts,hq,←ComparisonQuery.coverage.1 v lower d F]
    simp
  · rw [encodedComparisonQueryContexts,hq,←ComparisonQuery.coverage.1 v lower d F]
    simp

/-- All semantic normalizer data are obtained from the already checked actual
finite programme, rather than supplied as an extra source theorem premise. -/
theorem mixed_normalized_source (q : ComparisonQuery)
    (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (hlt : lower.1.repr<eta.1.repr) :
    ∃ (added : List (NONote × Nat)) (last : NONote),
      (encodedRangeRangeNormalization q.1).1=
        oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E) ∧
      (encodedRangeRangeNormalization q.1).2.1=rawNoteEncode last.1 ∧
      oneVariableComparisonValid (.range ((w++added)++[(last,c)]) E) ∧
      lower.1.repr≤last.1.repr ∧ last.1.repr≤eta.1.repr ∧
      (last.1.repr=lower.1.repr ∨ Order.IsSuccLimit last.1.repr) ∧
      ∀ x : Nat,encodedRangeRangeLocalTail q≤x →
        actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x=
          actualOneVariableComparisonValue (.range ((w++added)++[(last,c)]) E) x := by
  have hlo : 0<lower.1.repr := hS.2.1 (lower,d) (List.mem_append_right _ (List.mem_singleton_self _))
  obtain ⟨added,last,hsource,hcode,hvalid,hlow,hhigh,hweight,hstop,hadded,hN,heval⟩ :=
    SuccessorNormalization.actual_program.2 w E eta lower c hR hlo hlt
  have hnorm := mixed_normalization q w v eta lower c d E F hq hlt
  refine ⟨added,last,?_,?_,hvalid,hlow,hhigh,hstop,?_⟩
  · rw [hnorm]
    exact hsource
  · rw [hnorm]
    exact hcode
  · intro x hx
    have hbound : (encodedSuccessorNormalization (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode lower.1) c).2.2≤x := by
      rw [←hnorm]
      exact (normalization_tail_bound q).trans hx
    exact congrArg (fun p : Nat × Nat => p.1) (heval x hbound).2.2

theorem mixed_normalized_child (q : ComparisonQuery)
    (w v added : List (NONote × Nat)) (eta lower last : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(lower,d)]) F))
    (hq : MixedOrientations q (.range (w++[(eta,c)]) E) (.range (v++[(lower,d)]) F))
    (hlt : lower.1.repr<eta.1.repr)
    (hsource : (encodedRangeRangeNormalization q.1).1=
      oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E))
    (hcode : (encodedRangeRangeNormalization q.1).2.1=rawNoteEncode last.1) :
    (if last=lower then
      (oneVariableComparisonEncode (comparisonLiteralInner (w++added) E),
        oneVariableComparisonEncode (comparisonLiteralInner v F))
    else (oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E),
      oneVariableComparisonEncode (comparisonLiteralInner v F)))∈encodedComparisonChildren q.1.1 q.1.2 := by
  rw [mixed_children q w v eta lower c d E F hR hS hq hlt]
  have hnorm := mixed_normalization q w v eta lower c d E F hq hlt
  dsimp only [encodedComparisonMixedChildren]
  rw [ComparisonExpansion.outer_source,ComparisonExpansion.outer_source,
    ComparisonExpansion.prefix_program.2,←hnorm,hsource,hcode]
  by_cases heq : last=lower
  · subst last
    simp only [SourceKernelCalls.program.2,ite_true,List.mem_singleton]
  · have hne : rawNoteEncode last.1≠rawNoteEncode lower.1 := by
      intro h
      apply heq
      apply Subtype.ext
      have hh := congrArg rawNoteDecode h
      simpa only [rawNoteDecodeEncode last.1,rawNoteDecodeEncode lower.1] using hh
    simp only [if_neg heq,if_neg hne,SourceKernelCalls.program.2,List.mem_singleton]

end LogicLineages.OrdinalComparison.RangeRangeNode
