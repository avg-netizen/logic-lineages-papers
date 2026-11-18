module
public import LogicLineages.PermittedControl.ControlTargets
public import LogicLineages.PermittedControl.FactorialProof

@[expose] public section
namespace LogicLineages.PermittedControl

 theorem factorial_control_laws : Targets.ControlLaws factorialControl 0 :=
  ⟨factorialControl_even, factorialControl_primrec, factorialControl_ge,
    factorialControl_separation, factorialControl_lt_nextG,
    ⟨6, 101, factorialControl_eventual⟩, factorialControl_potential⟩

 theorem near_control_laws (b : Nat) : Targets.ControlLaws (nearControl b) (b + 1) :=
  ⟨nearControl_even b,
    nearControl_primrec.comp (Primrec.const b) Primrec.id,
    nearControl_ge b, nearControl_separation b, nearControl_lt_nextG b,
    ⟨6, 101, nearControl_eventual b⟩, nearControl_potential b⟩

 theorem fullControl : Targets.FullControl := ⟨factorial_control_laws, near_control_laws⟩

 theorem uniformFiniteLevel : Targets.UniformFiniteLevel :=
  ⟨6, 101, factorialControl_eventual, nearControl_eventual⟩

end LogicLineages.PermittedControl
