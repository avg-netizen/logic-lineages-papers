module
public import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsTargets
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsEnumProof
import LogicLineages.PermittedControl.ActualFiniteFullValueGuardsFoldProof
import LogicLineages.PermittedControl.ActualFullLabelPairGuardsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFiniteFullValueGuards
open OrdinalComparison FieldComparison PreparedProjection
open ActualFullValueLabels (Label)
open ActualFullLabelPairGuards (Pair Answer cost Ready PaidUpdate exactActualPairHasOutcome)

private theorem pairOrigin (ls : List Label) (p : Pair) (h : p ∈ pairs ls) :
    p.1 ∈ ls ∧ p.2 ∈ ls := by
  obtain ⟨a,ah,rem⟩ := List.mem_flatMap.mp h
  obtain ⟨b,bh,rfl⟩ := List.mem_map.mp rem
  exact ⟨ah,bh⟩

private theorem costLe (B : Nat) (ps : List Pair) (p : Pair) (h : p ∈ ps) :
    cost B p ≤ ps.foldr (fun q n => max (cost B q) n) 0 := by
  induction ps with
  | nil => cases h
  | cons a ps ih =>
      rcases List.mem_cons.mp h with eq | ht
      · subst a; exact le_max_left _ _
      · exact (ih ht).trans (le_max_right _ _)

private theorem pairReady (B : Nat) (ρ : Nat → Nat) (top : Nat) (ls : List Label)
    (ready : ReadyFamily B ρ top ls) :
    ∀ p ∈ pairs ls, Ready B ρ top p := by
  intro p inPairs
  obtain ⟨lhs,rhs⟩ := pairOrigin ls p inPairs
  obtain ⟨leftScope,leftProper⟩ := ready.1 p.1 lhs
  obtain ⟨rightScope,rightProper⟩ := ready.1 p.2 rhs
  have cost := costLe B (pairs ls) p inPairs
  exact ⟨leftScope,rightScope,leftProper,rightProper,
    fun lt => cost.trans (ready.2 p.1 lhs lt),fun lt => cost.trans (ready.2 p.2 rhs lt)⟩

private theorem pairPaid (B : Nat) (ρ : Nat → Nat) (top z : Nat) (ls : List Label)
    (paid : PaidFamily B ρ top z ls) :
    ∀ p ∈ pairs ls, PaidUpdate B ρ top z p := by
  intro p here
  obtain ⟨left,right⟩ := pairOrigin ls p here
  exact ⟨(costLe B (pairs ls) p here).trans paid.1,paid.2 p.1 left,paid.2 p.2 right⟩

private theorem actualMatches (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (ρ : Nat → Nat) (top z : Nat) (ps : List Pair)
    (ready : ∀ p ∈ ps, Ready B ρ top p) (paid : ∀ p ∈ ps, PaidUpdate B ρ top z p) :
    ∃ as : List Answer, as.length = ps.length ∧ Matches f (Function.update ρ top z) ps as := by
  induction ps with
  | nil => exact ⟨[],rfl,.nil⟩
  | cons p ps ih =>
      obtain ⟨a,_,h⟩ := exactActualPairHasOutcome f B hf ρ top z p
        (ready p List.mem_cons_self) (paid p List.mem_cons_self)
      obtain ⟨as,len,hs⟩ := ih (fun q qh => ready q (List.mem_cons_of_mem _ qh))
        (fun q qh => paid q (List.mem_cons_of_mem _ qh))
      exact ⟨a::as,congrArg Nat.succ len,.cons h hs⟩

theorem exactFiniteFullValueGuards : ExactFiniteFullValueGuards := by
  intro f B hf ρ top ls ready
  let ps := pairs ls
  have lower := pairReady B ρ top ls ready
  have construct (as : List Answer) (member : as ∈ patterns ps.length) :=
    exactOrderedGuardFold f B hf ρ top ps as ((exactFinitePatternEnumeration ps.length as).mp member) lower
  constructor
  · intro as member
    have result := construct as member
    refine ⟨result.1,result.2.1,?_⟩
    intro ν tied z paid
    exact result.2.2 ν tied z (pairPaid B ρ top z ls paid)
  · intro z paid
    have upper := pairPaid B ρ top z ls paid
    obtain ⟨as,len,hs⟩ := actualMatches f B hf ρ top z ps lower upper
    have member := (exactFinitePatternEnumeration ps.length as).mpr len
    have result := construct as member
    obtain ⟨ν,tie⟩ := result.2.1
    exact ⟨as,member,hs,ν,tie,(result.2.2 ν tie z upper).mpr hs⟩

end LogicLineages.PermittedControl.ActualFiniteFullValueGuards
