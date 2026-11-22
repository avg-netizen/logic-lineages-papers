module
public import LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReadsTargets
import LogicLineages.PermittedControl.EntryExistenceProof
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReads
open OrdinalComparison FieldComparison PreparedProjection
open MixedSameRankResidue (WeightedOperand properOperand orderedReads)
open ActualZeroClassReplacement (Read liftedReads)
open ActualFiniteGlobalTail (syntaxOf)
open ActualBoundedSignedRouteSemantics (stateSyntax)

theorem exactPaidOperandRead : ExactPaidOperandRead := by
  intro f B selected ρ op proper tail
  suffices found : ∃ v : Nat, LowerOperandActual f ρ op v by
    obtain ⟨v,actual⟩ := found
    exact ⟨v,actual,(preparedTiedProjection.1 f ρ op v).mpr actual⟩
  cases op with
  | coordinate rank => exact ⟨ρ rank,rfl⟩
  | ordinary rank field =>
    cases field with
    | iterate n => exact ⟨f^[n] (ρ rank),True.intro,rfl⟩
    | entry n lam mu =>
      have hp : ProperField (.entry n lam mu) := proper
      have paid : intervalMinimum lam mu ≤ ρ rank := tail
      obtain ⟨i,hit,_⟩ := entryExistenceOrbit f B selected lam.1.repr mu.1.repr (ρ rank)
        (rawNotation_repr_lt_epsilonZero lam.1) hp.1 hp.2.1 hp.2.2 paid
      exact ⟨f^[n] (entryNormAt f (countInitial lam.1.repr (ρ rank)) i),
        ⟨hp,(le_max_left _ _).trans ((le_max_right _ _).trans paid)⟩,i,hit,rfl⟩
  | count rank lam mu =>
    have hp : ProperField (.entry 0 lam mu) := proper
    have paid : intervalMinimum lam mu ≤ ρ rank := tail
    obtain ⟨i,hit,_⟩ := entryExistenceOrbit f B selected lam.1.repr mu.1.repr (ρ rank)
      (rawNotation_repr_lt_epsilonZero lam.1) hp.1 hp.2.1 hp.2.2 paid
    exact ⟨i,⟨hp,(le_max_left _ _).trans ((le_max_right _ _).trans paid)⟩,hit⟩

private theorem ceilingDominates (t : WeightedOperand) (ts : List WeightedOperand)
    (h : t ∈ ts) : operandMinimum t.2 ≤ readCeiling ts := by
  induction ts with
  | nil => cases h
  | cons u us ih =>
    change operandMinimum t.2 ≤ max (operandMinimum u.2) (readCeiling us)
    rcases List.mem_cons.mp h with first | rest
    · subst u
      exact le_max_left _ _
    · exact (ih rest).trans (le_max_right _ _)

private theorem ordered (f : Nat → Nat) (B : Nat) (selected : SelectedWithThreshold f B)
      (ρ : Nat → Nat) (ts : List WeightedOperand)
      (proper : ∀ t ∈ ts, properOperand t.2)
      (paid : ∀ t ∈ ts, operandMinimum t.2 ≤ ρ t.2.rank) :
    ∃ rs : List Read, rs.map Prod.fst = ts ∧ liftedReads f ρ rs := by
  induction ts with
  | nil => exact ⟨[],rfl,True.intro⟩
  | cons t ts ih =>
    obtain ⟨v,actual,read⟩ := exactPaidOperandRead f B selected ρ t.2
      (proper t List.mem_cons_self) (paid t List.mem_cons_self)
    obtain ⟨rs,frames,live⟩ := ih
      (fun u h => proper u (List.mem_cons_of_mem _ h)) (fun u h => paid u (List.mem_cons_of_mem _ h))
    exact ⟨(t,v)::rs,congrArg (List.cons t) frames,⟨actual,read,live⟩⟩

theorem exactPaidOrderedSyntaxReads : ExactPaidOrderedSyntaxReads := by
  intro f B selected ρ s proper paid
  obtain ⟨rs,frames,live⟩ := ordered f B selected ρ s.terms proper
    (fun t used => (ceilingDominates t s.terms used).trans (paid t used))
  refine ⟨⟨s.constant,rs⟩,?_,live⟩
  cases s with
  | mk c ts => exact congrArg (ActualSymbolicZeroSuccessor.SyntaxState.mk c) frames

end LogicLineages.PermittedControl.ActualPaidOrderedSyntaxReads
