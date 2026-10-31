module
public import LogicLineages.OrdinalComparison.WWOriginalDomainDefinitions
public import LogicLineages.OrdinalComparison.WWAdmissibleAssignmentDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalDomain
open AdmissibleSum AdmissibleAssignment

/-- Original Definition 2.18 assembled delta, with the exact repaired structural
policy macros. This is delta alone, not the source lambda assignment which
adds retained head closure. High actual coordinates are X-free on the source
domain; head closure changes context, not their ordinal value. -/
def delta {Γ : List Ty} {σ : Ty} {m : Nat} (p : Policy)
    (h : OrdinalVector (σ :: Γ) m) :
    Option (OrdinalVector Γ (max (σ.level + 1) m)) := do
  let ps ← collect (m + 1) (fun i => AdmissiblePartial.run p i.val (h i))
  let factor := 2 ^ (σ.level + 1) * ((List.ofFn h).map ordinalPartialSize).sum
  pure fun j =>
    if j.val = 0 then repeated p .scalarRepeat factor (ps 0 0)
    else if hj : j.val < σ.level + 2 then
      expand (p.shape .positiveAbstraction m) (fun i => ps i ⟨j.val, hj⟩)
    else ordinalHeadClosure (h ⟨j.val, by have := j.isLt; omega⟩)

end LogicLineages.OrdinalComparison.Source.OriginalDomain
