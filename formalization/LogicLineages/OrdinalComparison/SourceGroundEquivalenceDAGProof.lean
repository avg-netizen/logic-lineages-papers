module
public import LogicLineages.OrdinalComparison.SourceGroundEquivalenceTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.GroundEquivalence.Proof

theorem insert_values {Γ ss} (d : DAG Γ ss) {s} (r : Ref ss s) :
    d.insert.values (r.map insertSpec) = (d.values r).rename (insertGround Γ s.1) := by
  induction d generalizing s with
  | nil => cases r
  | var d x ih => cases r with
    | here => rfl
    | there r => exact ih r
  | app d f a ih => cases r with
    | here =>
      simp only [DAG.insert,DAG.values,Ref.map,insertSpec,extendValues,Term.rename]
      exact congrArg₂ Term.app (ih f) (ih a)
    | there r => exact ih r
  | lam d b ih => cases r with
    | here =>
      simp only [DAG.insert,DAG.values,Ref.map,insertSpec,extendValues,Term.rename]
      exact congrArg Term.lam (ih b)
    | there r => exact ih r
  | zero d ih => cases r with
    | here => rfl
    | there r => exact ih r
  | succ d ih => cases r with
    | here => rfl
    | there r => exact ih r
  | case d τ ih => cases r with
    | here => rfl
    | there r => exact ih r
  | recursor d τ ih => cases r with
    | here => rfl
    | there r => exact ih r

theorem magnify_input {Γ} (d : Input Γ .ground) : (magnifyInput d).term=magnify d.term := by
  change (Term.app (.lam (d.graph.insert.values (d.root.map insertSpec))) .zeroC : OriginalTerm Γ .ground) = _
  rw [insert_values]
  rfl

theorem lower_input {Γ} (d : Input Γ .ground) : (lowerInput d).term=lower d.term := by
  change .app identity (magnifyInput d).term=lower d.term
  rw [magnify_input]
  rfl

theorem upper_input {Γ} (d : Input Γ .ground) : (upperInput d).term=upper d.term := by
  change .app constant (magnifyInput d).term=upper d.term
  rw [magnify_input]
  rfl

theorem lower_size {Γ} (d : Input Γ .ground) : (lowerInput d).specs.length=d.specs.length+6 := by
  simp [lowerInput,identityInput,magnifyInput,List.length_map]
theorem upper_size {Γ} (d : Input Γ .ground) : (upperInput d).specs.length=d.specs.length+6 := by
  simp [upperInput,constantInput,magnifyInput,List.length_map]
end LogicLineages.OrdinalComparison.Source.GroundEquivalence.Proof
