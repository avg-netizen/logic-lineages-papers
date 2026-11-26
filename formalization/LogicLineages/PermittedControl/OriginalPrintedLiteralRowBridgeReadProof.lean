module
public import LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridgeTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridge
open PreparedProjection
open MixedSameRankResidue (WeightedOperand properOperand orderedReads actualSum)
open ActualZeroClassReplacement (Read liftedReads)
open ActualReadChargeIteration (ReadState stateValue)
open ActualBoundedSignedRouteSemantics (stateSyntax)
open ActualSymbolicZeroSuccessor (SyntaxState)
open OriginalPrintedTerminalBitClauses (ClauseHolds)

private theorem build (f ρ : Nat → Nat) (ts : List WeightedOperand) (vs : List Nat)
    (h : orderedReads f ρ ts vs) :
      ∃ rs : List Read, rs.map Prod.fst = ts ∧ rs.map Prod.snd = vs ∧ liftedReads f ρ rs := by
  induction ts generalizing vs with
  | nil =>
    cases vs with
    | nil => exact ⟨[],rfl,rfl,True.intro⟩
    | cons v vs => exact False.elim h
  | cons t ts ih =>
    cases vs with
    | nil => exact False.elim h
    | cons v vs =>
      obtain ⟨rs,terms,values,live⟩ := ih vs h.2.2
      exact ⟨(t,v)::rs,congrArg (List.cons t) terms,congrArg (List.cons v) values,h.1,h.2.1,live⟩

theorem exactActualRowReadState : ExactActualRowReadState := by
  intro f ρ c ts v
  constructor
  · rintro ⟨vs,ordered,result⟩
    obtain ⟨reads,terms,values,live⟩ := build f ρ ts vs ordered
    refine ⟨⟨c,reads⟩,congrArg (SyntaxState.mk c) terms,live,?_⟩
    change c + actualSum (reads.map Prod.fst) (reads.map Prod.snd) = v
    rw [terms,values]
    exact result
  · rintro ⟨s,frames,live,result⟩
    have terms : s.reads.map Prod.fst = ts := congrArg SyntaxState.terms frames
    have cEq : s.constant = c := congrArg SyntaxState.constant frames
    refine ⟨s.reads.map Prod.snd,?_ ,?_⟩
    · rw [← terms]
      exact live
    · change s.constant + actualSum (s.reads.map Prod.fst) (s.reads.map Prod.snd) = v at result
      rwa [cEq,terms] at result

private theorem properOne (f ρ : Nat → Nat) (op : LowerOperand) (v : Nat)
    (read : LowerOperandActual f ρ op v) : properOperand op := by
  cases op with
  | coordinate rank => trivial
  | ordinary rank field =>
    cases field with
    | iterate n => trivial
    | entry n lam mu => exact read.1.1
  | count rank lam mu => exact read.1.1

private theorem properTape (f ρ : Nat → Nat) (ts : List WeightedOperand) (vs : List Nat)
    (h : orderedReads f ρ ts vs) : ∀ t ∈ ts, properOperand t.2 := by
  induction ts generalizing vs with
  | nil => intro t used; cases used
  | cons t ts ih =>
    cases vs with
    | nil => exact False.elim h
    | cons v vs =>
      intro w used
      rcases List.mem_cons.mp used with first | tail
      · subst w
        exact properOne f ρ t.2 v h.1
      · exact ih vs h.2.2 w tail

theorem exactLiteralRowProper : ExactLiteralRowProper := by
  intro f ρ row paid
  obtain ⟨admitted,v,witness,_⟩ := paid
  obtain ⟨vs,reads,_⟩ := witness
  exact ⟨admitted,properTape f ρ row.1.2.2 vs reads⟩

theorem exactLiteralProperClauseFilter : ExactLiteralProperClauseFilter := by
  classical
  intro f ρ family
  constructor
  · rintro ⟨c,member,live⟩
    have proper : AdmittedLiteralClause c := fun r used => exactLiteralRowProper f ρ r (live r used)
    have filter : c ∈ properClauses family := by
      refine List.mem_filter.mpr ⟨member,?_⟩
      exact decide_eq_true_eq.mpr proper
    exact ⟨c,filter,live⟩
  · rintro ⟨c,kept,live⟩
    exact ⟨c,(List.mem_filter.mp kept).1,live⟩

end LogicLineages.PermittedControl.OriginalPrintedLiteralRowBridge
