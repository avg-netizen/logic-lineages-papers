module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.CoherenceProof
open NumberedMultisetNumeric

theorem frontierRank (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (hord : ∀ node param child, child ∈ d node param → m child param < m node param)
    (seed param depth node : Nat) (h : node ∈ frontierList d seed param depth) :
    m node param + depth ≤ m seed param := by
  induction depth generalizing node with
  | zero =>
    simp only [frontierList,Nat.rec_zero,List.mem_singleton] at h
    subst node
    exact Nat.le_refl _
  | succ depth ih =>
    obtain ⟨parent,hparent,hnode⟩ := List.mem_flatMap.mp h
    have hp := ih parent hparent
    have hn := hord parent param node hnode
    omega

theorem frontierEmpty (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (hord : ∀ node param child, child ∈ d node param → m child param < m node param)
    (seed param : Nat) :
    frontierList d seed param (m seed param + 1) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro node h
  have hb := frontierRank m d hord seed param _ node h
  omega

theorem graphCoherent (m : Nat → Nat → Nat) (d : Nat → Nat → List Nat)
    (g : Nat → List Nat → Nat → Option Nat) (f : Nat → Nat → Nat)
    (hord : ∀ node param child, child ∈ d node param → m child param < m node param)
    (hlayer : ∀ node param, g node ((d node param).map (fun child => f child param)) param = some (f node param))
    (seed param i : Nat) (hi : i ≤ m seed param + 1) :
    graphList m d g seed param i =
      (frontierList d seed param (m seed param + 1 - i)).map (fun node => (node,f node param)) := by
  induction i with
  | zero =>
    rw [Nat.sub_zero,frontierEmpty m d hord seed param]
    rfl
  | succ i ih =>
    have hi' : i ≤ m seed param + 1 := by omega
    have hprev : m seed param + 1 - i = (m seed param - i) + 1 := by omega
    have hnow : m seed param + 1 - (i+1) = m seed param - i := by omega
    rw [graphList,ih hi',hnow]
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro node hnode
    have hcover : ∀ child ∈ d node param,
        child ∈ frontierList d seed param (m seed param + 1 - i) := by
      intro child hc
      rw [hprev]
      exact List.mem_flatMap.mpr ⟨node,hnode,hc⟩
    rw [ExchangeGraphStage.NativeProof.coveredMap (d node param)
      (frontierList d seed param (m seed param + 1 - i)) (fun child => f child param) hcover]
    rw [hlayer]
    rfl

theorem nativeCoherentGraph : Targets.NativeCoherentGraph := by
  intro R D G m d g f hr hd hg hord hlayer i seed param hi
  rw [NativeProof.nativeGraph R D G m d g hr hd hg,
    graphCoherent m d g f hord hlayer seed param i hi]
  simp only [List.map_map,Function.comp_def]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.CoherenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.CoherenceProof
