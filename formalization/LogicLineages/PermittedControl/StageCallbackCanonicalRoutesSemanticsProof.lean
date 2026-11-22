module
public import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesTargets
import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesLayoutProof
import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesNodeProof
import LogicLineages.PermittedControl.ActualBoundedSignedRoutesProof
import LogicLineages.PermittedControl.ActualSyntaxChargeBudgetProof
import LogicLineages.PermittedControl.ActualPaidSignedRouteReplayContextProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
open OrdinalComparison
open ActualZeroClassReplacement (liftedReads)
open ActualCanonicalOperandGrouping (groupTyped)
open ActualCanonicalZeroTrace (CanonicalTrace CanonicalZeroWitness)
open ActualFullLabelPairGuards (Answer)
open ActualSymbolicZeroSuccessor (SyntaxState)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualBoundedSignedRoutes (Route PacketHolds RouteHolds prefixGuard exactPathLocalAvailability)
open ActualBoundedSignedRouteSemantics (stateSyntax)
open ActualRankedNormalizationSyntax (extend)
open ActualReadChargeIteration (ReadState stateValue stateCharge)
open ActualFiniteGlobalTail (syntaxOf)
open ActualSyntaxChargeBudget (syntaxBudget exactChargeBudget)
open ActualPaidSignedRouteReplay (exactActualReplayContext)

/-- A genuine canonical trace extended by one genuine zero witness. -/
theorem traceSnoc {f : Nat → Nat} {B : Nat} {ρ : Nat → Nat} {r top : Nat}
    {answers : List (List Answer)} {a : List Answer} {s t u : ReadState}
    (path : CanonicalTrace f B ρ r top answers s t) :
    CanonicalZeroWitness f B ρ r top t u a →
      CanonicalTrace f B ρ r top (answers ++ [a]) s u := by
  induction path with
  | nil s =>
      intro edge
      exact .cons edge (.nil u)
  | cons first rest ih =>
      intro edge
      exact .cons first (ih edge)

theorem exactCanonicalRouteSoundness : ExactCanonicalRouteSoundness := by
  intro f B baseline r top z initial ctx test positive fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro answers s path route member holds
      have layout := (exactCanonicalRouteLayout top fuel test positive (stateSyntax s) route).mp
        member
      rcases layout with ⟨inactive,rfl⟩ | ⟨active,a,ha,branches⟩
      · exact (exactCanonicalReachedLinear f B baseline r top z initial ctx answers s path
          inactive test positive).mp holds
      · have facts := (exactCanonicalReachedGuards f B baseline r top z initial ctx answers s
          path active).2.2
        rcases branches with ⟨nonzero,rfl⟩ | ⟨zero,k,out,depth,success,child,inChild,rfl⟩
        · have packet : PacketHolds f baseline top z (guard top (groupTyped (syntaxOf s)) a) :=
            holds.1 _ List.mem_cons_self
          rcases facts a ha packet with ⟨canceled,_⟩ | ⟨_,sign⟩
          · exact False.elim (nonzero canceled)
          · exact (sign test positive).mpr holds.2
        · have pair := (exactPathLocalAvailability f baseline top z test positive
            (guard top (groupTyped (syntaxOf s)) a) child).mp holds
          rcases facts a ha pair.1 with ⟨_,reachedOut,witness,exactOut,value,_⟩ | ⟨nonzero,_⟩
          · have eq : out = stateSyntax reachedOut :=
              Option.some.inj (success.symm.trans exactOut)
            have childMember : child ∈ routes top test positive k (stateSyntax reachedOut) :=
              eq ▸ inChild
            have valid := ih k (by omega) (answers ++ [a]) reachedOut (traceSnoc path witness)
              child childMember pair.2
            rw [value]
            exact valid
          · exact False.elim (nonzero zero)

theorem exactCanonicalRouteCompleteness : ExactCanonicalRouteCompleteness := by
  intro f B baseline r top z initial ctx test positive fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
      intro answers s path enough valid
      by_cases active : CanonicalActive top (syntaxOf s)
      · obtain ⟨_,⟨a,listed,passing⟩,real⟩ := exactCanonicalReachedGuards f B baseline r top z
          initial ctx answers s path active
        rcases real a listed passing with ⟨zero,out,witness,literal,value,strict⟩ | ⟨nonzero,sign⟩
        · let k := fuel-1
          have depth : fuel = k+1 := by dsimp [k]; omega
          have smaller : k < fuel := by omega
          have paid : stateCharge r out ≤ k := by dsimp [k]; omega
          have childTruth : test.test.atPolarity positive (stateValue out) := by
            rwa [← value]
          obtain ⟨child,atChild,childPasses⟩ :=
            ih k smaller (answers ++ [a]) out (traceSnoc path witness) paid childTruth
          let route := prefixGuard (guard top (groupTyped (syntaxOf s)) a) child
          have chosen : route ∈ routes top test positive fuel (stateSyntax s) :=
            (exactCanonicalRouteLayout top fuel test positive (stateSyntax s) route).mpr
              (Or.inr ⟨active,a,listed,
                Or.inr ⟨zero,k,stateSyntax out,depth,literal,child,atChild,rfl⟩⟩)
          exact ⟨route,chosen,(exactPathLocalAvailability f baseline top z test positive
            (guard top (groupTyped (syntaxOf s)) a) child).mpr ⟨passing,childPasses⟩⟩
        · let route := signedRoute top (stateSyntax s) a
          have chosen : route ∈ routes top test positive fuel (stateSyntax s) :=
            (exactCanonicalRouteLayout top fuel test positive (stateSyntax s) route).mpr
              (Or.inr ⟨active,a,listed,Or.inl ⟨nonzero,rfl⟩⟩)
          refine ⟨route,chosen,?_,(sign test positive).mp valid⟩
          intro p used
          have eq : p = guard top (groupTyped (syntaxOf s)) a := List.mem_singleton.mp used
          rw [eq]
          exact passing
      · let route := linearRoute top test positive (stateSyntax s)
        have chosen : route ∈ routes top test positive fuel (stateSyntax s) :=
          (exactCanonicalRouteLayout top fuel test positive (stateSyntax s) route).mpr
            (Or.inl ⟨active,rfl⟩)
        exact ⟨route,chosen,(exactCanonicalReachedLinear f B baseline r top z initial ctx
          answers s path active test positive).mpr valid⟩

theorem exactCanonicalSufficientRoutes : ExactCanonicalSufficientRoutes := by
  intro f B baseline r top z initial ctx test positive
  constructor
  · exact exactCanonicalRouteCompleteness f B baseline r top z initial ctx test positive
      (syntaxBudget r (syntaxOf initial)) [] initial (.nil initial) (exactChargeBudget.1 r initial)
  · rintro ⟨route,member,passes⟩
    exact exactCanonicalRouteSoundness f B baseline r top z initial ctx test positive
      (syntaxBudget r (syntaxOf initial)) [] initial (.nil initial) route member passes

theorem exactCanonicalRoutesAcrossReplay : ExactCanonicalRoutesAcrossReplay := by
  intro f B selected r top baseline s setup z minimum signPaid test positive
  obtain ⟨ex,ready⟩ := exactActualReplayContext f B selected r top baseline s setup z minimum
  have actual (original : ReadState) (frames : stateSyntax original = s)
      (live : liftedReads f (Function.update baseline top z) original.reads) :
      (test.test.atPolarity positive (stateValue original) ↔
        ∃ path ∈ routes top test positive (syntaxBudget r s.terms) s,
          RouteHolds f baseline top z test positive path) := by
    have terms : syntaxOf original = s.terms := congrArg SyntaxState.terms frames
    have constant : original.constant = s.constant := congrArg SyntaxState.constant frames
    have ctx : CanonicalContext f B baseline r top z original :=
      ⟨ready original frames live,by rw [terms,constant]; exact signPaid⟩
    have known := exactCanonicalSufficientRoutes f B baseline r top z original ctx test positive
    rw [terms,frames] at known
    exact known
  constructor
  · rintro ⟨source,frames,live,sign⟩
    exact (actual source frames live).mp sign
  · intro someRoute
    obtain ⟨original,frames,live⟩ := ex
    exact ⟨original,frames,live,(actual original frames live).mpr someRoute⟩

end LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
