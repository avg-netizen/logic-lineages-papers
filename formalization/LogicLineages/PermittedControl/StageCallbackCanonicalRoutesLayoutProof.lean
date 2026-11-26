module
public import LogicLineages.PermittedControl.StageCallbackCanonicalRoutesTargets
import LogicLineages.PermittedControl.ActualBoundedSignedRoutesProof
import LogicLineages.PermittedControl.ActualFullLabelPairGuardsLowerProof
import LogicLineages.PermittedControl.ActualPreparedSlotAppendProof
import LogicLineages.PermittedControl.HighFieldPreparedPacketShapeProof
import LogicLineages.PermittedControl.StableSortedHighFieldPacketProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualPreparedSlotAppend (Packet exactPreparedAppend)
open ActualSignedOrdinaryPairHigh (OrderTest orientedPacket strictPacket equalPacket)
open ActualBoundedSignedRoutes (Tip Route prefixGuard)
open ActualFullLabelPairGuards (Pair Answer ActualOutcome lowerShape)
open ActualFiniteFullValueGuards (pairs patterns compile Matches)
open ActualFullValueLabels (labels ActualLabel)
open ActualFullValueMaximalMetadata (maximalCoefficient)
open ActualCanonicalOperandGrouping (groupTyped)
open ActualCanonicalSymbolicZeroSuccessor (canonicalSuccessor)
open ActualCanonicalTerminalTruth (canonicalPacket)
open ActualSelectedSignedRoutePacket (Shape terminalPacket signedBit)
open MixedSameRankResidue (WeightedOperand)
open ActualSymbolicZeroSuccessor (SyntaxState)
open OriginalMatrixLinearRowFormula (safeTruth safeFalsity safeTest safePolarity)
open StableSortedHighField (basePacket basePacketExact appendOrderShape)

theorem branchLayout (top : Nat) (s : SyntaxState)
    (next : SyntaxState → List Route) (answer : List Answer) (route : Route) :
    route ∈ branchRoutes top s next answer ↔
      (maximalCoefficient (groupTyped s.terms) answer ≠ 0 ∧ route = signedRoute top s answer) ∨
      (maximalCoefficient (groupTyped s.terms) answer = 0 ∧ ∃ out,
        canonicalSuccessor s.constant s.terms answer = some out ∧
        ∃ child ∈ next out, route = prefixGuard (guard top (groupTyped s.terms) answer) child) := by
  by_cases cancel : maximalCoefficient (groupTyped s.terms) answer = 0
  · cases produced : canonicalSuccessor s.constant s.terms answer with
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

theorem nodeLayout (top : Nat) (test : OrderTest) (positive : Bool) (s : SyntaxState)
    (next : SyntaxState → List Route) (route : Route) :
    route ∈ nodeRoutes top test positive s next ↔
      (¬ CanonicalActive top s.terms ∧ route = linearRoute top test positive s) ∨
      (CanonicalActive top s.terms ∧ ∃ a ∈ tapes (groupTyped s.terms),
        route ∈ branchRoutes top s next a) := by
  by_cases yes : CanonicalActive top s.terms
  · simp [nodeRoutes,yes,List.mem_flatMap]
  · simp [nodeRoutes,yes]

theorem exactCanonicalRouteLayout : ExactCanonicalRouteLayout := by
  intro top n test positive s route
  cases n with
  | zero =>
      refine (nodeLayout top test positive s (fun _ => []) route).trans ?_
      simp [branchLayout]
  | succ n =>
      refine (nodeLayout top test positive s (routes top test positive n) route).trans ?_
      simp [branchLayout]

private theorem strictShape (F G : ValueField) (lo : Nat) (c : Int) (k : OrderTest) (pos : Bool) :
    Shape (strictPacket F G lo c k pos) := by
  let base := basePacket F G lo (ActualSignedOrdinaryPairHigh.request k c).1
  have ready : PreparedInput base.1 base.2 :=
    (basePacketExact F G lo (lo+1) _ (Nat.lt_succ_self lo)).2
  exact appendOrderShape base.1 _ lo (safePolarity _ _ ready _)

private theorem orientedShape (F G : ValueField) (i j : Nat) (c : Int) (k : OrderTest)
    (pos : Bool) : Shape (orientedPacket F G i j c k pos) := by
  unfold orientedPacket
  split
  · exact strictShape _ _ _ _ _ _
  · split
    · exact strictShape _ _ _ _ _ _
    · change PreparedInput [] (OriginalMatrixLinearRowFormula.choosePolarity _ _)
      exact safePolarity _ _ (HighFieldPreparedPacket.packetShape.2.1 _ _ _) _

private theorem pairShape (top : Nat) (p : Pair) (a : Answer) :
    Shape (ActualFullLabelPairGuards.packet top p a) := by
  unfold ActualFullLabelPairGuards.packet
  split
  · exact lowerShape _ _
  · exact orientedShape _ _ _ _ _ _ _

/-- Every compiled comparison guard is a prepared input, for any pair
list and any tape, including mismatched lengths. -/
theorem compileShape (top : Nat) (ps : List Pair) (as : List Answer) :
    Shape (compile top ps as) := by
  induction ps generalizing as with
  | nil =>
    cases as with
    | nil => exact safeTruth []
    | cons a as => exact safeFalsity []
  | cons p ps ih =>
    cases as with
    | nil => exact safeFalsity []
    | cons a as =>
      exact (exactPreparedAppend _ _ (pairShape top p a) (ih as)).1

private theorem namesShape (n : Nat) (xs : List WeightedOperand) :
    ∀ t ∈ ActualSyntaxLinearTerminal.names n xs,
      ∃ i : Nat, t.2 = .variable i ∧ i < n+xs.length := by
  induction xs generalizing n with
  | nil => intro t used; cases used
  | cons x xs ih =>
    intro t used
    rcases List.mem_cons.mp used with first | rest
    · subst t
      exact ⟨n,rfl,by simp only [List.length_cons]; omega⟩
    · obtain ⟨i,eq,bound⟩ := ih (n+1) t rest
      exact ⟨i,eq,by simp only [List.length_cons]; omega⟩

/-- The canonical linear exit is a prepared input for every literal term
list; no read or activity hypothesis. -/
theorem canonicalPacketShape (top : Nat) (constant : Int) (raw : List WeightedOperand)
    (test : OrderTest) (pos : Bool) :
    Shape (canonicalPacket top constant raw test.test pos) := by
  let terms := groupTyped raw
  let low := ActualSyntaxLinearTerminal.lower top terms
  let ops := low.map Prod.snd
  let row := ActualSyntaxLinearTerminal.termsRow top constant terms
  have plain : PlainPreparedRow row := by
    intro t used
    rcases List.mem_cons.mp used with first | rest
    · subst t
      exact ⟨0,rfl⟩
    · obtain ⟨i,eq,_⟩ := namesShape 1 low t rest
      exact ⟨i,eq⟩
  have bounds : ∀ n ∈ NormalForm.rowVariables row, n ≤ ops.length := by
    intro n used
    obtain ⟨t,member,rfl⟩ := List.mem_map.mp used
    rcases List.mem_cons.mp member with first | rest
    · subst t
      exact Nat.zero_le _
    · obtain ⟨i,eq,bound⟩ := namesShape 1 low t rest
      change t.2.name ≤ ops.length
      rw [eq]
      change i ≤ ops.length
      simpa only [ops,List.length_map,Nat.add_comm 1,Nat.lt_succ_iff] using bound
  exact safePolarity ops _ (safeTest ops test.test row plain bounds) pos

theorem signedPacketShape (test : OrderTest) (pos : Bool) (coef : Int) :
    Shape (terminalPacket test pos (.signed coef)) := by
  let selected := if pos then signedBit test coef else !(signedBit test coef)
  change PreparedInput [] (if selected then .truth else .falsity)
  by_cases passes : selected = true
  · rw [if_pos passes]
    exact safeTruth []
  · rw [if_neg passes]
    exact safeFalsity []

theorem exactCanonicalRouteShape : ExactCanonicalRouteShape := by
  intro top fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro test positive s path member
    rcases (exactCanonicalRouteLayout top fuel test positive s path).mp member with idle | active
    · obtain ⟨_,rfl⟩ := idle
      exact ⟨fun p used => False.elim (List.not_mem_nil used),
        canonicalPacketShape top s.constant s.terms test positive⟩
    · obtain ⟨_,a,_,br⟩ := active
      rcases br with tip | more
      · obtain ⟨_,rfl⟩ := tip
        refine ⟨?_,signedPacketShape _ _ _⟩
        intro p used
        have eq := List.mem_singleton.mp used
        rw [eq]
        exact compileShape _ _ _
      · obtain ⟨_,k,out,depth,_,tail,htail,rfl⟩ := more
        have lt : k < fuel := by omega
        obtain ⟨shapeGuard,shapeTip⟩ := ih k lt test positive out tail htail
        refine ⟨?_,shapeTip⟩
        intro p used
        rcases List.mem_cons.mp used with first | rest
        · rw [first]
          exact compileShape _ _ _
        · exact shapeGuard p rest

theorem answerCodeInjective (a b : Answer) (h : a.code = b.code) : a = b := by
  cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

theorem outcomeUnique (f θ : Nat → Nat) (p : Pair) (a b : Answer)
    (ha : ActualOutcome f θ p a) (hb : ActualOutcome f θ p b) : a = b := by
  obtain ⟨u,v,lu,lv,ca⟩ := ha
  obtain ⟨u',v',lu',lv',cb⟩ := hb
  have eu : u = u' := Option.some.inj (Option.some.inj (lu.2.2.symm.trans lu'.2.2))
  have ev : v = v' := Option.some.inj (Option.some.inj (lv.2.2.symm.trans lv'.2.2))
  rw [eu,ev] at ca
  exact answerCodeInjective a b (ca.symm.trans cb)

theorem exactMatchedAnswerUnique : ExactMatchedAnswerUnique := by
  intro f θ ps
  induction ps with
  | nil =>
    intro a b ha hb
    cases ha
    cases hb
    rfl
  | cons p ps ih =>
    intro a b ha hb
    cases ha with
    | cons ha1 ha2 =>
      cases hb with
      | cons hb1 hb2 =>
        rw [outcomeUnique f θ p _ _ ha1 hb1,ih _ _ ha2 hb2]

end LogicLineages.PermittedControl.StageCallbackCanonicalRoutes
