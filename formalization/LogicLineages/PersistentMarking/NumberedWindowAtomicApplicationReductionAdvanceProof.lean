module
public import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionTargets
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionRunProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicLeastChecks
import LogicLineages.PersistentMarking.NumberedWindowAtomicRawStepChecks

public section
namespace LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionAdvanceProof
open NumberedWindowAtomicApplicationTargets NumberedWindowAtomicApplicationReductionTargets
open NumberedWindowAtomicApplicationReductionRunProof (concreteStep)
open NumberedWindowAtomicApplicationChecks (exact_AtomicAuxLeast)
open NumberedWindowAtomicLeastChecks (exact_AtomicLeastSingleton)
open NumberedWindowAtomicRawStepChecks (exact_AtomicRawFields)
open NumberedWindowAtomicRawStep (freeRaw bottomRaw)
open NumberedWindowConcreteCheckers (step)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings least)
open NumberedWindowPositivePathAlgorithm (advance hopView)

private theorem checkedHop (runStep : Nat → Nat → Nat → Bool) (leastOf : Nat → Option Nat)
    {source code y : Nat} (h : advance runStep leastOf (some source) code = some y) :
    ∃ q w r, hopView code = some (y,q,w,r) ∧ runStep q w r = true ∧
      leastOf q = some source ∧ leastOf r = some y := by
  cases hv : hopView code with
  | none => simp [advance,hv] at h
  | some hop =>
    rcases hop with ⟨target,q,w,r⟩
    have hc : (if runStep q w r && (leastOf q == some source) && (leastOf r == some target)
        then some target else none) = some y := by
      simpa only [advance,Option.bind_eq_bind,Option.bind_some,hv] using h
    by_cases accepted : (runStep q w r && (leastOf q == some source) &&
        (leastOf r == some target)) = true
    · rw [if_pos accepted] at hc
      have hy := Option.some.inj hc
      simp only [Bool.and_eq_true,beq_iff_eq,and_assoc] at accepted
      exact ⟨q,w,r,by rw [hy],accepted.1,accepted.2.1,hy ▸ accepted.2.2⟩
    · rw [if_neg accepted] at hc
      cases hc

theorem auxAdvance : ExactAtomicAuxAdvance := by
  intro xs s Γ requested dom cod fn arg code y atom checked
  obtain ⟨q,w,r,seen,used,sourceLeast,resultLeast⟩ :=
    checkedHop (step xs s Γ requested) (least s Γ requested) checked
  obtain ⟨argRaw,predecessor,traceIn⟩ :=
    (exact_AtomicAuxLeast s Γ requested dom cod fn arg q atom).2 sourceLeast
  subst q
  obtain ⟨present,shape⟩ := concreteStep xs s Γ requested dom cod fn argRaw w r atom used
  refine ⟨_,w,r,argRaw,seen,rfl,used,present,sourceLeast,resultLeast,traceIn,?_⟩
  rcases shape with ⟨wrapper,bottom⟩ | ⟨stored,name,child,headFree,wrapper,nested,changed⟩
  · have bottomLeast : least s Γ requested (bottomRaw cod) = some y := bottom ▸ resultLeast
    have out := (exact_AtomicLeastSingleton s Γ requested cod).2.2 y bottomLeast
    exact Or.inl ⟨wrapper,bottom,out⟩
  · have nextLeast : least s Γ requested (auxRaw dom cod (bottomRaw stored) argRaw) = some y :=
      changed ▸ resultLeast
    obtain ⟨outArg,target,traceOut⟩ :=
      (exact_AtomicAuxLeast s Γ requested dom cod (bottomRaw stored) argRaw y
        (AtomHead.bottom stored)).1 nextLeast
    exact Or.inr ⟨stored,name,child,outArg,headFree,wrapper,nested,changed,target,traceOut⟩

theorem image {xs : Entries} {s : Settings} {Γ : List Nat}
    {requested dom cod fn arg code y : Nat}
    (h : AuxAcceptedHop xs s Γ requested dom cod fn arg code y) :
    y = bottomRaw cod ∨
      ∃ stored name a, fn = freeRaw stored name ∧ y = auxRaw dom cod (bottomRaw stored) a := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,shape⟩ := h
  rcases shape with ⟨_,_,rooted⟩ | ⟨stored,name,_,a,free,_,_,_,moved,_⟩
  · exact Or.inl rooted
  · exact Or.inr ⟨stored,name,a,free,moved⟩

theorem bottomFunctionImage {xs : Entries} {s : Settings} {Γ : List Nat}
    {requested dom cod stored arg code y : Nat}
    (h : AuxAcceptedHop xs s Γ requested dom cod (bottomRaw stored) arg code y) :
    y = bottomRaw cod := by
  rcases image h with done | ⟨t,n,_,bad,_⟩
  · exact done
  · exact False.elim (exact_AtomicRawFields.2.2.1 t n stored bad.symm)

end LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationReductionAdvanceProof
