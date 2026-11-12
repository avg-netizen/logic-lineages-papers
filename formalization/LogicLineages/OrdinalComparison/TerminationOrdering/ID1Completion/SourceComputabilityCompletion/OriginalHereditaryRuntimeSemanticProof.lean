module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryTypedJobProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeIterationCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAgendaDefinitions OriginalHereditaryExpectedDefinitions OriginalHereditaryWorkBound
open OriginalHereditaryRuntimeSemanticDefinitions OriginalHereditaryRuntimeIterationDefinitions

theorem surround (f : Nat → Nat) (k x y z out : Nat)
 (hv : f x = y) (hc : f^[k] y = z) (hr : f z = out) :
 f^[k+2] x = out := by
 rw [show k+2 = (k+1)+1 by omega,Function.iterate_succ_apply,hv,
   Function.iterate_succ_apply',hc,hr]

theorem depthExecution : OriginalHereditaryRuntimeSemanticTargets.DepthExecution := by
 intro localReturn R n arity c depth
 induction depth with
 | zero =>
   intro a suffix old ha terminal
   have hj : jobs c a = [] := by
     simp only [jobs,terminal a.core (Path.refl a.core),decorate]
   have hv := OriginalHereditaryRuntimeSemanticStepProof.visit R c a suffix old
   rw [hj] at hv
   have hrel : List.Forall₂ (Expected arity R c) (jobs c a) [] := by rw [hj]; exact .nil
   obtain ⟨v,he,hr⟩ := OriginalHereditaryRuntimeSemanticStepProof.returning
     localReturn R arity c a [] suffix old ha hrel
   refine ⟨v,he,?_⟩
   change (tick R)^[0+2] _ = _
   exact surround (tick R) 0 _ _ _ _ hv rfl hr
 | succ depth ih =>
   intro a suffix old ha terminal
   have each : ∀ b ∈ jobs c a, ∀ tail values, ∃ value, Expected arity R c b value ∧
       (tick R)^[2 * visits depth b.core] (state c (.visit b :: tail) values) =
         state c tail (value :: values) := by
     intro b hb tail values
     apply ih b tail values (OriginalHereditaryTypedJobProof.expansionClosure n arity c a b ha hb)
     intro t ht
     exact terminal t (Path.cons (OriginalHereditaryAgendaProof.jobsMember a b hb) ht)
   obtain ⟨values,hvalues,hchildren⟩ := OriginalHereditaryRuntimeSemanticListProof.listExecution
     R arity c (fun b => 2 * visits depth b.core) (jobs c a) each (.returning a :: suffix) old
   obtain ⟨value,hvalue,hreturn⟩ := OriginalHereditaryRuntimeSemanticStepProof.returning
     localReturn R arity c a values suffix old ha hvalues
   refine ⟨value,hvalue,?_⟩
   have he := surround (tick R) _ _ _ _ _
     (OriginalHereditaryRuntimeSemanticStepProof.visit R c a suffix old) hchildren hreturn
   rw [OriginalHereditaryAgendaProof.jobsCost] at he
   have hc : 2 * ((successors a.core).map (visits depth)).sum + 2 = 2 * visits (depth+1) a.core := by
     simp only [visits]; omega
   rw [hc] at he
   exact he

theorem exactExecution : OriginalHereditaryRuntimeSemanticTargets.ExactExecution := by
 intro localReturn R n arity c a suffix old ha
 obtain ⟨value,hv,he⟩ := depthExecution localReturn R n arity c (weight a.core) a suffix old ha
   (fun t ht => OriginalHereditaryWorkBoundProof.terminalAtDepth a.core t ht)
 refine ⟨value,hv,?_⟩
 rw [OriginalHereditaryRuntimeIterationCalibrationProof.calibration]
 exact he

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeSemanticProof
