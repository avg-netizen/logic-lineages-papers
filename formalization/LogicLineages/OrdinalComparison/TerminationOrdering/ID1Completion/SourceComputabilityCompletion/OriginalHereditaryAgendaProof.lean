module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaTargets
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaProof
open OriginalHereditaryAgendaDefinitions OriginalHereditaryWorkBound

theorem trans {n c k l : Nat} {a b z : List (Frame n)}
 (h : Trace c k a b) (g : Trace c l b z) : Trace c (k+l) a z := by
 induction h with
 | refl => simpa using g
 | step h tail ih => simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using Trace.step h (ih g)

theorem listTrace {n c : Nat} (f : Job n → Nat) (as : List (Job n))
 (h : ∀ a ∈ as, ∀ suffix, Trace c (f a) (Frame.visit a :: suffix) suffix)
 (suffix : List (Frame n)) : Trace c ((as.map f).sum) (as.map Frame.visit ++ suffix) suffix := by
 induction as with
 | nil => exact Trace.refl _
 | cons a as ih =>
   have ha := h a (List.mem_cons_self) (as.map Frame.visit ++ suffix)
   have ht := ih (fun b hb => h b (List.mem_cons_of_mem a hb))
   simpa only [List.map_cons,List.sum_cons,List.cons_append] using trans ha ht

theorem decorateCore {n c : Nat} (a : Job n) (index : Nat) (ss : List (State (Fin n))) :
 (decorate c a index ss).map Job.core = ss := by
 induction ss generalizing index with
 | nil => rfl
 | cons s ss ih => simp only [decorate,List.map_cons,child,ih]

theorem jobsCore {n c : Nat} (a : Job n) : (jobs c a).map Job.core = successors a.core := decorateCore a 0 _

theorem jobsMember {n c : Nat} (a b : Job n) (h : b ∈ jobs c a) : b.core ∈ successors a.core := by
 rw [← jobsCore (c:=c) a]
 exact List.mem_map.mpr ⟨b,h,rfl⟩

theorem jobsCost {n c depth : Nat} (a : Job n) :
 ((jobs c a).map (fun b => 2 * visits depth b.core)).sum =
 2 * ((successors a.core).map (visits depth)).sum := by
 rw [← jobsCore (c:=c) a,List.map_map]
 induction jobs c a with
 | nil => rfl
 | cons b bs ih => simp only [List.map_cons,List.sum_cons,Nat.mul_add,ih]

theorem depthTrace : OriginalHereditaryAgendaTargets.DepthTrace := by
 intro n c depth
 induction depth with
 | zero =>
   intro a suffix h
   have he := h a.core (Path.refl a.core)
   have hj : jobs c a = [] := by simp only [jobs,he,decorate]
   have hv := Step.visit (c:=c) a suffix
   rw [hj] at hv
   simpa only [visits,List.map_nil,List.nil_append] using
     Trace.step hv (Trace.step (Step.returning a suffix) (Trace.refl suffix))
 | succ depth ih =>
   intro a suffix h
   have each : ∀ b ∈ jobs c a, ∀ tail, Trace c (2 * visits depth b.core) (Frame.visit b :: tail) tail := by
     intro b hb tail
     apply ih b tail
     intro t ht
     exact h t (Path.cons (jobsMember a b hb) ht)
   have ht := listTrace (fun b => 2 * visits depth b.core) (jobs c a) each (Frame.returning a :: suffix)
   have hr := Trace.step (Step.returning (c:=c) a suffix) (Trace.refl suffix)
   have hs := Trace.step (Step.visit (c:=c) a suffix) (trans ht hr)
   rw [jobsCost] at hs
   simpa only [visits,Nat.mul_add,Nat.mul_one,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs

theorem boundedTrace : OriginalHereditaryAgendaTargets.BoundedTrace := by
 intro n c a suffix
 refine ⟨2 * totalWork a.core,rfl,?_,?_⟩
 · exact Nat.mul_le_mul_left 2 (OriginalHereditaryWorkBoundProof.workBound (Fin n) a.core)
 · exact depthTrace n c (weight a.core) a suffix (fun t ht => OriginalHereditaryWorkBoundProof.terminalAtDepth a.core t ht)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaProof
