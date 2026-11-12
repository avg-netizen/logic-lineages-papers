module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityDependencyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryNativeBoundProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryNativeBoundDefinitions OriginalHereditaryFiniteObserver OriginalHereditaryFiniteStability OriginalHereditaryFiniteStabilityTargets

theorem stable : Stable := by
 intro R n arity c s depth
 induction depth generalizing s with
 | zero =>
   intro h
   have hp := NumberedAuxiliaryEnumerationSupportProof.sizePositive s.term.2
   simp only [weight] at h
   omega
 | succ depth ih =>
   intro h
   apply OriginalHereditaryFiniteStabilityDependencyProof.localDependency R (family R (depth+1)) (family R depth) n arity c s
   intro t ht
   apply ih t
   have hw := OriginalHereditaryNativeBoundProof.stepWeight ht
   omega

theorem settled : Settled := by
 intro R n arity c s depth h
 obtain ⟨extra,rfl⟩ := Nat.exists_eq_add_of_le h
 induction extra with
 | zero => simp
 | succ extra ih =>
   rw [Nat.add_succ,stable R n arity c s (weight s + extra) (Nat.le_add_right _ _),ih]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFiniteStabilityProof
