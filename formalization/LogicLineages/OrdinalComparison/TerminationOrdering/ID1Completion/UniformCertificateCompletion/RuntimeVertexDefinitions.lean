module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftPathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformParameterLeavesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertex
open Source

/-- Original raw vertex on [parameter,domain,codomain,RAWargument,value].
Read one original Gamma from the parameter Object decoder and retain the
caller's raw context code. No source window or Gamma is captured. -/
def value (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5) : Nat :=
  ((InternalOriginalUniformParameterLeaves.parameterObject 0 (v.get 0)).map (fun obj =>
    ApplicationCertificateLiftPath.vertex n arity obj.1 (Nat.unpair (v.get 0)).1
      (v.get 1) (v.get 2) (v.get 3) (v.get 4))).getD 0

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.RuntimeVertex
