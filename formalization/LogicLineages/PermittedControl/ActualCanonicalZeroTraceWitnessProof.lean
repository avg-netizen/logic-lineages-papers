module
public import LogicLineages.PermittedControl.ActualCanonicalZeroTraceTargets
import LogicLineages.PermittedControl.ActualCanonicalSymbolicZeroSuccessorProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalZeroTrace
open ActualCanonicalSymbolicZeroSuccessor
open ActualZeroClassCohortTransfer ActualZeroClassRecombinedRow ActualZeroClassReplacement
open ActualShortCountCleanup

theorem exactCanonicalZeroWitness : ExactCanonicalZeroWitness := by
  intro f B selected ρ strict r top s xs anns C a input
  obtain ⟨moved,ledger,x₀,q,moves,movedReads,anchor,origins,equations,replacement,cleaned,_⟩ :=
    exactCanonicalSuccessorWitness f B selected ρ strict C r s.constant s.reads xs anns a
      input.live (fun rd used => (input.ranks rd used).1) input.grouped input.aligned
      input.guards.1 input.nonempty input.matched input.maximum input.zero input.ready input.transfer
  let before := outsideCohort f C (xs.map Prod.fst) (xs.map Prod.snd) anns ++ moved
  let installed := s.constant + (replaceRow f C (xs.map Prod.fst) (xs.map Prod.snd) anns).2
  exact ⟨⟨installed + shortShift before,retained before⟩,
    xs,anns,C,moved,ledger,x₀,q,input,moves,movedReads,anchor,origins,equations,
    replacement,cleaned,rfl,rfl⟩

end LogicLineages.PermittedControl.ActualCanonicalZeroTrace
