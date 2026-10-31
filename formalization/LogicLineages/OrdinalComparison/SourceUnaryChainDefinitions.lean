module
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceUnaryChain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics

def chainBody {Γ : List Ty} :
    List (OriginalTerm Γ (.arrow .ground .ground)) → OriginalTerm (.ground :: Γ) .ground
  | [] => .var .here
  | v :: vs => .app (v.rename (Renaming.weaken Γ .ground)) (chainBody vs)

/-- One actual final abstraction. Every supplied operator keeps its literal
source syntax, including its scalar; typed weakening makes the new x fresh
without capture even through operators' existing nested binders. -/
def chainSource {Γ : List Ty} (vs : List (OriginalTerm Γ (.arrow .ground .ground))) :
    OriginalTerm Γ (.arrow .ground .ground) := .lam (chainBody vs)

/-- The manuscript's natural ordinal sum Σ(V_j,1+3)+1. -/
noncomputable def headSum {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal) :
    List (OrdinalVector Γ 1) → Ordinal
  | [] => 1
  | v :: vs => ordinalNaturalSum (ordinalNaturalSum (denote ν (v 1)) 3) (headSum ν vs)
end LogicLineages.OrdinalComparison.Source.SourceUnaryChain
