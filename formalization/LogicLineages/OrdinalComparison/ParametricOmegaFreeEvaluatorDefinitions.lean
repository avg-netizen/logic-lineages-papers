module
public import LogicLineages.OrdinalComparison.OrdinalSyntaxComputableFoldDefinitions
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableDefinitions
public import LogicLineages.OrdinalComparison.SourceRestrictedAssignmentFiniteDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator
abbrev Parameter := Nat × List Nat
def leaf (p : Parameter × Nat) : Nat :=
  if p.2=1 then 1 else if p.2%8=3 then p.1.2.getD (p.2/8) 0 else 0
noncomputable def branch (H : Nat × Nat → Nat) (p : Parameter × (Nat × Nat × Nat)) : Nat :=
  if p.2.1=4 then p.2.2.1+p.2.2.2 else
  if p.2.1=5 then 2^p.2.2.1*p.2.2.2 else
  if p.2.1=6 then ParametricPairCollapseComputable.actualValue H (p.1.1,p.2.2.1,p.2.2.2)
  else 0
noncomputable def evaluate (H : Nat × Nat → Nat) (i : Nat) (env : List Nat) (code : Nat) : Nat :=
  OrdinalSyntaxComputableFold.indexedFold leaf (branch H) (i,env) code
end LogicLineages.OrdinalComparison.Source.ParametricOmegaFreeEvaluator
