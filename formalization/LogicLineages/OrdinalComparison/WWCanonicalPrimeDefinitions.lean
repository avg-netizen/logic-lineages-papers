module
public import LogicLineages.OrdinalComparison.WWCanonicalBoxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source

abbrev OriginalTerm (Γ : List Ty) (τ : Ty) := Term Empty Empty.elim Γ τ

/-- Exact prime fragment of the actual typed original-T kernel. Application
and abstraction are explicitly not processed by this prime-only function. -/
def ordinalCanonicalPrime {Γ : List Ty} {τ : Ty} (t : OriginalTerm Γ τ) :
    Option (OrdinalVector Γ τ.level) :=
  match t with
  | .var v => some (fun i => .var ⟨_, v, i⟩)
  | .zeroC => some (fun _ => .one)
  | .succC => some (fun _ => .one)
  | .caseC _ => some (fun _ => .one)
  | .recC σ => some (fun i => if i.val = 0 then .add .one .one
      else if i.val = σ.level + 2 then .omega else .one)
  | .app _ _ | .lam _ => none
  | .ranked s _ => nomatch s

/-- Literal box followed by truncation at the actual result type level. -/
def ordinalCanonicalApplication {Γ : List Ty} {σ τ : Ty}
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level) :
    OrdinalVector Γ τ.level :=
  fun i => ordinalCanonicalBox f g
    ⟨i.val, Nat.lt_of_lt_of_le i.isLt (Nat.succ_le_succ (Nat.le_max_right _ _))⟩

end LogicLineages.OrdinalComparison.Source
