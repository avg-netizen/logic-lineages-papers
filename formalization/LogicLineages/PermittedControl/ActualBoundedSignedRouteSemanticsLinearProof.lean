module
public import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsTargets
import LogicLineages.PermittedControl.ActualBoundedSignedRouteSemanticsContextProof
import LogicLineages.PermittedControl.ActualSyntaxLinearTerminalProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
open ActualRankedNormalizationSyntax (extend)
open ActualBoundedSignedRoutes (PacketHolds RouteHolds linearRoute)
open ActualSyntaxLinearTerminal (packet exactActualSyntaxLinearTerminal)
open ActualFiniteGlobalTail (syntaxOf)
open ActualReadChargeIteration (stateValue)
open PreparedProjection

theorem exactReachedLinearRoute : ExactReachedLinearRoute := by
  intro f B baseline r top z initial ctx n s path inactive test positive
  let θ := extend baseline top z
  let raw := syntaxOf s
  let q := packet top s.constant raw test.test positive
  obtain ⟨live,ranks⟩ := reachedLiveAndRank path (sourceLive ctx) ctx.ranks
  have scope (t) (h : t ∈ raw) : t.2.rank ≤ top := by
    obtain ⟨rd,read,rfl⟩ := List.mem_map.mp h
    exact (ranks rd read).2
  have admitted : test.test.Admitted := by cases test <;> trivial
  obtain ⟨xs,_,_,supplies,checks⟩ :=
    exactActualSyntaxLinearTerminal f θ top s.constant raw s.reads rfl scope live inactive test.test positive admitted
  have topValue : θ top = z := (contextExtension ctx).2.1
  have fit (ν : Nat → Nat) :
      PreparedTableTied f top baseline q.1 ν ↔ PreparedTableTied f top θ q.1 ν :=
    tiedBelow f baseline θ top q.1 ν (contextBelow baseline top z)
  have real (ν : Nat → Nat) (tied : PreparedTableTied f top θ q.1 ν) :
      q.2.eval (Function.update ν 0 z) ↔ test.test.atPolarity positive (stateValue s) := by
    have actual := (checks ν tied).2.2.1
    rw [topValue] at actual
    exact actual
  constructor
  · rintro ⟨_,ν,tied,passes⟩
    exact (real ν ((fit ν).mp tied)).mp passes
  · intro valid
    obtain ⟨ν,tied⟩ := supplies
    exact ⟨fun g used => False.elim (List.not_mem_nil used),
      ν,(fit ν).mpr tied,(real ν tied).mpr valid⟩

end LogicLineages.PermittedControl.ActualBoundedSignedRouteSemantics
