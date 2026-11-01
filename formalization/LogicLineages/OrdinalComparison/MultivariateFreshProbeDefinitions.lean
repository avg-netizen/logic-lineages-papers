module
public import LogicLineages.OrdinalComparison.MultivariatePositiveRayDefinitions
public import LogicLineages.OrdinalComparison.InterpretedCollectedDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- A source-admissible fresh fixed head omega*(cap+i+1). Its raw code is
larger than cap, so it cannot be any head in a source whose code is ≤cap. -/
def positiveVariableHead (cap i : Nat) : NONote :=
  ⟨.oadd 1 ⟨cap+i+1,by omega⟩ 0,
    ONote.NF.oadd ONote.nf_one _ ONote.NFBelow.zero⟩

def positiveVariableHeadIndex (cap : Nat) (rho : NONote) : Option Nat :=
  match rho.1 with
  | .zero => none
  | .oadd e c t =>
    if e=1 ∧ t=0 ∧ cap<(c : Nat) then some ((c : Nat)-cap-1) else none

/-- Semantic retraction only: the equality ALGORITHM never evaluates this
supplied valuation or treats this head interpretation as a solver oracle. -/
noncomputable def positiveRetractedHead (cap : Nat) (ρ : Nat → Nat)
    (rho : NONote) (z : Nat) : Nat :=
  ((positiveVariableHeadIndex cap rho).map ρ).getD (actualProfileHead rho z)

def multivariatePositiveProbe (cap : Nat) : MultivariatePositiveExpr → FixedLimitPositiveExpr
  | .constant c => .constant c
  | .input i => .head (positiveVariableHead cap i) .input
  | .add E F => .add (multivariatePositiveProbe cap E) (multivariatePositiveProbe cap F)
  | .head rho E => .head rho (multivariatePositiveProbe cap E)

def multivariateHeadsSatisfy (P : NONote → Prop) : MultivariatePositiveExpr → Prop
  | .constant _ => True
  | .input _ => True
  | .add E F => multivariateHeadsSatisfy P E ∧ multivariateHeadsSatisfy P F
  | .head rho E => P rho ∧ multivariateHeadsSatisfy P E

def PositiveProbeHeadClosure (cap : Nat) (rho : NONote) : Prop :=
  rawNoteEncode rho.1≤cap ∨ (positiveVariableHeadIndex cap rho).isSome=true

end LogicLineages.OrdinalComparison
