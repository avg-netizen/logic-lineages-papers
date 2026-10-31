module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomatonTargets
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerProjectionStatementChecks
public import LogicLineages.ModelsAlgebra.Forests.ForestParseRepresentationCountsStatementChecks
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton.Proof
open RankedParse ProfileAutomatonEncoding ForestParseRepresentationCotree ForestParseRepresentationStates
open CotreePresburger CotreePresburgerTransition FirstOrder Language

 theorem state_ext {Q : Type} {s t : State Q} (hk : stateKind s = stateKind t)
    (hS : stateSubset s = stateSubset t) : s = t := by
  change ofLex s = ofLex t
  exact Prod.ext hk hS

theorem allowed_expected (M : Machine) (o : Operation) (C : Cotree) :
    allowed o (expected M C) = true ↔ root C ≠ some o := by
  cases C with
  | atom => cases o <;> simp [allowed,expected,stateKind,mkState,kind,opKind,root]
  | node p n c => cases p <;> cases o <;> simp [allowed,expected,stateKind,mkState,kind,opKind,root]

theorem projection_expected (M : Machine) [LinearOrder M.State] n (c : Fin n → Cotree) :
    projectedCounts stateSubset (fun a => (List.ofFn (fun i => expected M (c i))).count a) =
      ForestParseRepresentationCounts.childCounts M c := by
  funext B
  have hp : projectedCounts stateSubset (fun a => (List.ofFn (fun i => expected M (c i))).count a) B =
      ((List.ofFn (fun i => expected M (c i))).map stateSubset).count B := by
    simpa only [List.count, Bool.beq_eq_decide_eq] using
      (CotreePresburgerProjection.StatementChecks.projectedWordCounts M.State (State M.State)
        stateSubset (List.ofFn (fun i => expected M (c i))) B)
  rw [hp]
  have he : (List.ofFn (fun i => expected M (c i))).map stateSubset =
      List.ofFn (fun i => stateSet M (c i)) := by
    simp [List.map_ofFn,expected,stateSubset,mkState,Function.comp_def]
  rw [he]
  exact ForestParseRepresentationCounts.StatementChecks.childCountExact M n c B

theorem nodeStepExact : Targets.NodeStepExact := by
  intro M _ o n c s
  simp only [nodeFormula, Formula.realize_inf, CotreePresburger.Proof.realize_truth]
  rw [CotreePresburgerTransition.StatementChecks.horizontalFormulaExact M.State (State M.State),
    projection_expected M (n+2) c]
  have htotal : (∑ a : State M.State, (List.ofFn (fun i => expected M (c i))).count a) =
      (List.ofFn (fun i => expected M (c i))).length := by
    simpa only [List.count, Bool.beq_eq_decide_eq] using
      (CotreePresburgerProjection.StatementChecks.wordTotalCounts (State M.State)
        (List.ofFn (fun i => expected M (c i))))
  have hguard : (∀ a : State M.State, allowed o a = false →
      (List.ofFn (fun i => expected M (c i))).count a = 0) ↔
      ∀ a ∈ List.ofFn (fun i => expected M (c i)), allowed o a = true := by
    simpa only [List.count, Bool.beq_eq_decide_eq] using
      (CotreePresburgerProjection.StatementChecks.allowedWordCounts (State M.State) (allowed o)
        (List.ofFn (fun i => expected M (c i))))
  rw [htotal,hguard]
  have hallow : (∀ a ∈ List.ofFn (fun i => expected M (c i)), allowed o a = true) ↔
      ∀ i, root (c i) ≠ some o := by
    constructor
    · intro h i
      exact (allowed_expected M o (c i)).mp (h _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    · intro h a ha
      rcases List.mem_ofFn.mp ha with ⟨i,rfl⟩
      exact (allowed_expected M o (c i)).mpr (h i)
  rw [hallow,List.length_ofFn]
  have harity : 2 ≤ n+2 := by omega
  simp only [harity,true_and]
  have hstate (q : M.State) : q ∈ stateSet M (.node o n c) ↔
      (formula (M.node o) q).Realize (ForestParseRepresentationCounts.childCounts M c) :=
    CotreeMachineParikh.StatementChecks.stateTransitionExact M o n c q
  constructor
  · rintro ⟨hk,hS,ha⟩
    refine ⟨state_ext hk ?_,ha⟩
    change stateSubset s = stateSet M (.node o n c)
    exact Finset.ext (fun q => (hS q).trans (hstate q).symm)
  · rintro ⟨rfl,ha⟩
    exact ⟨rfl,fun q => hstate q,ha⟩

theorem run_forward (M : Machine) [LinearOrder M.State] {C s} (h : Runs M C s) :
    Reduced C ∧ s = expected M C := by
  induction h with
  | atom =>
    refine ⟨trivial,?_⟩
    simp [leafState,expected,kind,ForestParseRepresentationStates.StatementChecks.stateSetLeaf M]
  | @node o n c v s children step ih =>
    have hv : v = fun i => expected M (c i) := funext (fun i => (ih i).2)
    rw [hv] at step
    have hs := (nodeStepExact M o n c s).mp step
    exact ⟨fun i => ⟨(ih i).1,hs.2 i⟩,hs.1⟩

theorem run_expected (M : Machine) [LinearOrder M.State] (C : Cotree) :
    Reduced C → Runs M C (expected M C) := by
  induction C with
  | atom =>
    intro _
    have he : expected M .atom = leafState M := by
      simp [expected,kind,leafState,ForestParseRepresentationStates.StatementChecks.stateSetLeaf M]
    rw [he]
    exact Runs.atom
  | node o n c ih =>
    intro hred
    exact Runs.node (fun i => expected M (c i)) (expected M (.node o n c))
      (fun i => ih i (hred i).1)
      ((nodeStepExact M o n c _).mpr ⟨rfl,fun i => (hred i).2⟩)

theorem runsExact : Targets.RunsExact := by
  intro M _ C s
  constructor
  · exact run_forward M
  · rintro ⟨h,hs⟩
    rw [hs]
    exact run_expected M C h

theorem runsDeterministic : Targets.RunsDeterministic := by
  intro M _ C s t hs ht
  exact (runsExact M C s).mp hs |>.2.trans ((runsExact M C t).mp ht).2.symm

theorem acceptanceExact : Targets.AcceptanceExact := by
  intro M _ C
  constructor
  · rintro ⟨s,hs,ha⟩
    obtain ⟨hred,rfl⟩ := (runsExact M C s).mp hs
    refine ⟨hred,(ForestParseRepresentationStates.StatementChecks.stateSetAcceptExact M C hred).mp ?_⟩
    simpa [accept,expected,stateSubset,mkState] using ha
  · rintro ⟨hred,ht⟩
    refine ⟨expected M C,run_expected M C hred,?_⟩
    have ha := (ForestParseRepresentationStates.StatementChecks.stateSetAcceptExact M C hred).mpr ht
    simpa [accept,expected,stateSubset,mkState] using ha

end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerAutomaton.Proof
