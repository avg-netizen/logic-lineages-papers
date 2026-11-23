module
public import LogicLineages.StandardControlCurrent.PolicyIndexedAssignmentTargets
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceDefinitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedSourceCompile
open OrdinalComparison Source Source.AdmissibleSum Source.ForwardTranslation
open Nat.Partrec (Code)
open PolicyIndexedAssignment (Abstraction ImplementsAbstraction Node)

abbrev Args := Code × Nat × Nat

/-- Absence of a ranked root row (not possible at implementing codes) is
not relabeled as the original assignment's returned failure. -/
noncomputable def finish (row : Option PolicyIndexedAssignment.Value) : Part (Option EncodedVector) :=
  (Part.ofOption row).map (fun assigned => assigned.bind compileVectorCode)

noncomputable def compile (abs : Abstraction) (x : Args) : Part (Option EncodedVector) :=
  (PolicyIndexedAssignment.run abs (x.1,List.replicate x.2.1 0,x.2.2)).bind finish

def ExactPolicyIndexedSourceCompile : Prop :=
  ∀ (abs : Abstraction) (c : Code) (p : Policy), PolicyIndexedShape.Implements c p →
    ImplementsAbstraction abs c p → ∀ depth code,
      compile abs (c,depth,code) = Part.some (PolicySourceInterface.compile p depth code)

def PolicyIndexedSourceCompileEffectivity : Prop :=
  ∀ abs : Abstraction, Partrec (PolicyIndexedAssignment.run abs) → Partrec (compile abs)

end LogicLineages.StandardControlCurrent.PolicyIndexedSourceCompile
