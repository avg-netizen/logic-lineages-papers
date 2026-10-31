module
public import LogicLineages.OrdinalComparison.WWDefaultPolicyDefinitions
public import LogicLineages.OrdinalComparison.WWOriginalSupportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open OriginalDomain

/-- Actual canonical scalar from the full default-policy assignment. The zero
fallback is explicit for failed assignments; totality and genuine finite,
positive scalar denotation on the original domain are proved, not assumed. -/
noncomputable def rawScalar {Γ : List Ty} (ν : OrdinalComponent Γ → Ordinal)
    (t : OriginalTerm Γ .ground) : Nat :=
  ((AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t).map
    (fun v => finiteValue (denote ν (v 0)))).getD 0

/-- The binder is genuinely fresh: typed weakening moves every existing
variable beneath the new head, recursively lifting under inner binders. -/
def eraser {Γ : List Ty} (a b : OriginalTerm Γ .ground) : OriginalTerm Γ .ground :=
  .app (.lam (a.rename (Renaming.weaken Γ .ground))) b

def detectorLeft {Γ} (p q : OriginalTerm Γ .ground) : OriginalTerm Γ .ground :=
  eraser (eraser p p) (eraser q q)
def detectorRight {Γ} (p q : OriginalTerm Γ .ground) : OriginalTerm Γ .ground :=
  eraser (eraser p q) (eraser q p)

noncomputable def g (n : Nat) : Nat := actualCollapse (Ordinal.omega0 + (n : Ordinal))

def CollisionAt {Γ} (ν : OrdinalComponent Γ → Ordinal)
    (p q : OriginalTerm Γ .ground) : Prop :=
  rawScalar ν (detectorRight p q) ≤ rawScalar ν (detectorLeft p q) ∧
  (rawScalar ν (detectorLeft p q) = rawScalar ν (detectorRight p q) ↔
    rawScalar ν p = rawScalar ν q) ∧
  (rawScalar ν p ≠ rawScalar ν q →
    2 ≤ rawScalar ν (detectorLeft p q) - rawScalar ν (detectorRight p q))
end LogicLineages.OrdinalComparison.Source.SourceCollisionCompletion
