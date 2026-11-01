module
public import LogicLineages.OrdinalComparison.RangeRangeNodeTailProof
public import LogicLineages.OrdinalComparison.RangeRangeNodeSourceProof
public import LogicLineages.OrdinalComparison.ComparisonQueryProof
public import LogicLineages.OrdinalComparison.ComparisonNodeTailProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem child_record (q : ComparisonQuery) (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (E F : OneVariableComparisonExpr)
    (hchild : (oneVariableComparisonEncode E,oneVariableComparisonEncode F)∈encodedComparisonChildren q.1.1 q.1.2)
    (profiles : Nat × Nat) (hp : profiles∈encodedComparisonQueryRequests q) :
    ∃ result : ComparisonNodeResult,
      (((oneVariableComparisonEncode E,oneVariableComparisonEncode F),profiles),result)∈table ∧
      actualComparisonQueryCorrect ((oneVariableComparisonEncode E,oneVariableComparisonEncode F),profiles) result := by
  apply hc
  exact (ComparisonQuery.child_projection _ _).mpr ⟨hchild,hp⟩

theorem equal_child_member (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range (w++[(eta,c)]) E))
    (hS : oneVariableComparisonValid (.range (v++[(eta,d)]) F))
    (hq : q.1=(oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F))) :
    (oneVariableComparisonEncode (comparisonLiteralInner w E),oneVariableComparisonEncode (comparisonLiteralInner v F))∈
      encodedComparisonChildren q.1.1 q.1.2 := by
  have hGuard : ¬(encodedComparisonSourceDomain (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))≠1 ∨
      encodedComparisonSourceDomain (oneVariableComparisonEncode (.range (v++[(eta,d)]) F))≠1) := by
    rw [ComparisonSourceDomain.correct _ hR,ComparisonSourceDomain.correct _ hS]
    simp
  have hmodR : oneVariableComparisonEncode (.range (w++[(eta,c)]) E)%2=1 := by
    change (2*Nat.pair _ _+1)%2=1
    omega
  have hmodS : oneVariableComparisonEncode (.range (v++[(eta,d)]) F)%2=1 := by
    change (2*Nat.pair _ _+1)%2=1
    omega
  rw [hq,←SourceKernelCalls.program.2 w eta c E,←SourceKernelCalls.program.2 v eta d F]
  unfold encodedComparisonChildren
  rw [if_neg hGuard]
  simp only [hmodR,hmodS,Nat.one_ne_zero,if_false,ComparisonExpansion.outer_source,if_true,List.mem_singleton]

theorem equal_eta_candidate (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : q.1=(oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F))) : rawNoteEncode eta.1∈eta_candidates q := by
  unfold eta_candidates
  rw [hq,ComparisonExpansion.outer_source w eta c E]
  exact List.mem_cons_self

theorem equal_mass_bound (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : q.1=(oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F))) :
    encodedPrincipalKernelMassModulus (rawNoteEncode eta.1) c d≤encodedRangeRangeLocalTail q := by
  have h := mass_bound q (rawNoteEncode eta.1) (equal_eta_candidate q w v eta c d E F hq)
  simpa only [hq,ComparisonExpansion.outer_source] using h

theorem equal_profile_bounds (q : ComparisonQuery) (w v : List (NONote × Nat)) (eta : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr)
    (hq : q.1=(oneVariableComparisonEncode (.range (w++[(eta,c)]) E),
      oneVariableComparisonEncode (.range (v++[(eta,d)]) F)))
    (P : Nat) (hP : P∈[q.2.1,q.2.2,1]) :
    encodedLimitPairCertificateTail (rawNoteEncode eta.1) P c d≤encodedRangeRangeLocalTail q ∧
    encodedLimitPairCertificateTail (rawNoteEncode eta.1) P d c≤encodedRangeRangeLocalTail q ∧
    encodedKernelProfileLeafTail (encodedComparisonPrincipalNote (rawNoteEncode eta.1)) P c≤encodedRangeRangeLocalTail q ∧
    encodedKernelProfileLeafTail (encodedComparisonPrincipalNote (rawNoteEncode eta.1)) P d≤encodedRangeRangeLocalTail q := by
  have h := profile_bounds q (rawNoteEncode eta.1) (equal_eta_candidate q w v eta c d E F hq) P hP
  simpa only [hq,ComparisonExpansion.outer_source] using h

end LogicLineages.OrdinalComparison.RangeRangeNode
