module
public import LogicLineages.PermittedControl.ActualBoundedSignedRoutesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBoundedSignedRoutes
open PreparedProjection
open MixedSameRankResidue (WeightedOperand)
open ActualSymbolicZeroSuccessor (SyntaxState successor)
open ActualRankedNormalizationSyntax (normalizedTerms)
open ActualFiniteSignedNodeBranch (nodePattern nodePacket nodeCoefficient StaticActive)
open ActualFullLabelPairGuards (Answer)
open ActualSignedOrdinaryPairHigh (OrderTest)
open ActualMixedRowLeadingAnnotations (NonlinearOperand)
open ActualPreparedSlotAppend (Packet)

private theorem nonlinearExact (op : LowerOperand) : nonlinear op = true ↔ NonlinearOperand op := by
  cases op with
  | coordinate r => simp [nonlinear,NonlinearOperand]
  | count r l m => simp [nonlinear,NonlinearOperand]
  | ordinary r F =>
      cases F <;> simp [nonlinear,NonlinearOperand,SelectedNonlinearImageBounds.NonlinearField]

theorem exactActiveSyntax : ExactActiveSyntax := by
  intro top raw
  simp only [active,List.any_eq_true,activeTest,Bool.and_eq_true,decide_eq_true_eq,nonlinearExact,
    StaticActive,and_assoc]

theorem exactPathLocalAvailability : ExactPathLocalAvailability := by
  intro f baseline top z test positive g tail
  change (((∀ h ∈ g::tail.guards, PacketHolds f baseline top z h)) ∧
      TipHolds f baseline top z test positive tail.tip) ↔ _
  constructor
  · rintro ⟨reads,tip⟩
    exact ⟨reads g List.mem_cons_self,fun h used => reads h (List.mem_cons_of_mem _ used),tip⟩
  · rintro ⟨head,rest,tip⟩
    refine ⟨?_,tip⟩
    intro p used
    rcases List.mem_cons.mp used with eq | more
    · simpa only [eq] using head
    · exact rest p more

private theorem branchLayout (top : Nat) (s : SyntaxState)
    (next : SyntaxState → List Route) (answer : List Answer) (route : Route) :
    route ∈ branchRoutes top s next answer ↔
      (nodeCoefficient s.terms answer ≠ 0 ∧ route = signedRoute top s answer) ∨
      (nodeCoefficient s.terms answer = 0 ∧ ∃ out,
        successor s.constant s.terms answer = some out ∧
        ∃ child ∈ next out, route = prefixGuard (nodePacket s.terms top answer) child) := by
  by_cases cancel : nodeCoefficient s.terms answer = 0
  · cases produced : successor s.constant s.terms answer with
    | none => simp [branchRoutes,cancel,produced]
    | some out =>
        rw [branchRoutes,if_pos cancel,produced]
        constructor
        · intro member
          obtain ⟨child,here,eq⟩ := List.mem_map.mp member
          exact Or.inr ⟨cancel,out,rfl,child,here,eq.symm⟩
        · rintro (⟨different,_⟩ | ⟨_,val,eq,child,here,exactRoute⟩)
          · exact False.elim (different cancel)
          · have same := Option.some.inj eq
            subst val
            exact List.mem_map.mpr ⟨child,here,exactRoute.symm⟩
  · simp [branchRoutes,cancel]

private theorem nodeLayout (top : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState)
    (next : SyntaxState → List Route) (route : Route) :
    route ∈ nodeRoutes top test positive s next ↔
      (¬ StaticActive top s.terms ∧ route = linearRoute top test positive s) ∨
      (StaticActive top s.terms ∧ ∃ a ∈ nodePattern s.terms, route ∈ branchRoutes top s next a) := by
  by_cases yes : StaticActive top s.terms
  · have e := (exactActiveSyntax top s.terms).mpr yes
    simp [nodeRoutes,e,yes,List.mem_flatMap]
  · have e : ¬ active top s.terms = true := fun h => yes ((exactActiveSyntax top s.terms).mp h)
    simp [nodeRoutes,e,yes]

theorem exactTypedRouteLayout : ExactTypedRouteLayout := by
  intro top n test positive s route
  cases n with
  | zero =>
      refine (nodeLayout top test positive s (fun _ => []) route).trans ?_
      simp [branchLayout]
  | succ n =>
      refine (nodeLayout top test positive s (routes top test positive n) route).trans ?_
      simp [branchLayout]

end LogicLineages.PermittedControl.ActualBoundedSignedRoutes
