module
public import LogicLineages.OrdinalComparison.WWAdmissibleSumDefinitions
public import LogicLineages.OrdinalComparison.WWGeneratedGradeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.AdmissiblePartial
open AdmissibleSum

def three {Γ : List Ty} (p : Policy) (site : MacroSite)
    (a b c : OrdinalExpression Γ) : OrdinalExpression Γ :=
  expand (p.shape site 2) (fun i => if i.val = 0 then a else if i.val = 1 then b else c)

def twice {Γ : List Ty} (p : Policy) (a : OrdinalExpression Γ) : OrdinalExpression Γ :=
  expand (p.shape .positiveRepeat 1) (fun _ => a)

/-- Actual literal partial for every structural source policy. The outer
active exponential sum has three operands, with Repeat2 retained as its
unchanged first operand. No association selector examines an input tree. -/
def run {Γ : List Ty} {σ : Ty} (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) : Option (OrdinalPartialVector Γ σ) :=
  if ordinalHeadFree t then some (ordinalFreePartialVector i t) else
  match t with
  | .var ⟨_, _, k⟩ => if i = k.val then some (fun _ => .one) else none
  | .zero | .one | .omega => none
  | .add f g => do
      let pf ← run p i f
      let pg ← run p i g
      pure fun j => three p .activeAdd (pf j) (pg j) .one
  | .emul f g => if 0 < i then do
      let pf ← run p (i + 1) f
      let pg ← run p i g
      pure fun j => three p .activeExp (twice p (pf j)) (pg j) .one
    else none
  | .collapse f g => if i = 0 then do
      let pf ← run p 1 f
      let pg ← run p 0 g
      pure fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
        else .add (pf j) (pg j)
    else none

end LogicLineages.OrdinalComparison.Source.AdmissiblePartial
