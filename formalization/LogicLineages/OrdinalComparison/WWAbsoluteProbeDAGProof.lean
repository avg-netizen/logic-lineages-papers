module
public import LogicLineages.OrdinalComparison.WWAbsoluteProbeDAGTargets
public import LogicLineages.OrdinalComparison.WWGroundClosingAssignmentProof
public import LogicLineages.OrdinalComparison.WWScopedSourceDAGProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG.Proof
open GroundEquivalence GroundClosing

theorem map_values {Γ Δ ss} (r : GroundMap Γ Δ) (d : DAG Γ ss) {s} (x : Ref ss s) :
    (mapGraph r d).values x=(d.values x).substitute (GroundMap.source (prefixMap r s.1)) := by
  induction d generalizing s with
  | nil => cases x
  | var d y ih =>
    cases h : prefixMap r _ y with
    | var z => cases x with
      | here => simp [mapGraph,h,DAG.values,extendValues,Term.substitute,GroundMap.source,Image.source]
      | there x => simpa only [mapGraph,h,DAG.values,extendValues] using ih x
    | zero => cases x with
      | here => simp [mapGraph,h,DAG.values,extendValues,Term.substitute,GroundMap.source,Image.source]
      | there x => simpa only [mapGraph,h,DAG.values,extendValues] using ih x
  | app d f a ih => cases x with
    | here => exact congrArg₂ Term.app (ih f) (ih a)
    | there x => exact ih x
  | lam d b ih => cases x with
    | here =>
      simp only [mapGraph,DAG.values,extendValues,Term.substitute]
      rw [← GroundClosing.Proof.source_lift]
      exact congrArg Term.lam (ih b)
    | there x => exact ih x
  | zero d ih => cases x with
    | here => rfl
    | there x => exact ih x
  | succ d ih => cases x with
    | here => rfl
    | there x => exact ih x
  | case d τ ih => cases x with
    | here => rfl
    | there x => exact ih x
  | recursor d τ ih => cases x with
    | here => rfl
    | there x => exact ih x

theorem substitution : Targets.Substitution := by
  intro Γ Δ τ r d
  exact ⟨map_values r d.graph d.root,rfl⟩

theorem closing : Targets.Closing := by
  intro Γ τ hΓ d
  exact ⟨(substitution Γ [] τ (AbsoluteObserver.closingMap hΓ) d).1,rfl⟩

theorem probe : Targets.Probe := by
  intro Γ τ d x
  constructor
  · change (Term.app (.lam .zeroC) (.app (.lam (d.graph.insert.values (d.root.map insertSpec))) (.var x)) : OriginalTerm Γ .ground)=_
    rw [GroundEquivalence.Proof.insert_values]
    rfl
  · simp [probeInput,List.length_map]

theorem original : Targets.Original := by
  intro Γ τ d
  unfold originalInput
  constructor
  · rw [(probe _ _ _ _).1,(ScopedDAG.Proof.«renaming» _ _ _ _ _).1]
    rfl
  · exact (probe _ _ _ _).2

theorem closed : Targets.Closed := by
  intro Γ τ hΓ d
  unfold closedInput
  constructor
  · rw [(probe _ _ _ _).1,(ScopedDAG.Proof.«renaming» _ _ _ _ _).1,(closing Γ τ hΓ d).1]
    rfl
  · exact (probe _ _ _ _).2
end LogicLineages.OrdinalComparison.Source.AbsoluteProbeDAG.Proof
