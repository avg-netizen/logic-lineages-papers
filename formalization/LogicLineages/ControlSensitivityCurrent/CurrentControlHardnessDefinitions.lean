module
public import LogicLineages.ControlSensitivityCurrent.PolicyProgramComparisonTargets
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionDefinitions
public import LogicLineages.OrdinalComparison.SourceBlankHaltingUniversalityDefinitions
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentControlHardness

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open ExistentialPlan GroundEquivalence PolicyProgramComparisonTargets

def queryHolds (strict : Bool) (p : AdmissibleSum.Policy) (f : Nat → Nat) {Γ}
    (a b : OriginalTerm Γ .ground) : Prop :=
  if strict then Strict p f a b else Weak p f a b

def rawMember (strict : Bool) (p : AdmissibleSum.Policy) (f : Nat → Nat) (code : Nat) : Prop :=
  ∃ (n : Nat) (a b : OriginalTerm (List.replicate n Ty.ground) .ground),
    SourceMachineQueryCode.unpack code = some (n, SyntaxCode.encodeTerm a, SyntaxCode.encodeTerm b) ∧
      queryHolds strict p f a b

def member (strict : Bool) (p : AdmissibleSum.Policy) (b code : Nat) : Prop :=
  SourceGammaRestrictedReduction.RestrictedSyntax code ∧
    rawMember strict p (SourceMachineControlNonperiodicity.gamma b) code

def output (strict : Bool) (b e : Nat) : Nat :=
  if strict then SourceMachineQueryCode.output b e else SourceGammaWeakCodedReduction.output b e

abbrev ctx (b e : Nat) := (compile (SourceMachineConjunctionPlan.plan b e)).context

def weakDAG (b e : Nat) : Input (ctx b e) .ground × Input (ctx b e) .ground :=
  let pair := strictPair (SourceMachineConjunctionPlan.plan b e)
  (constantInput pair.1, identityInput pair.2)

def dagPair (strict : Bool) (b e : Nat) : Input (ctx b e) .ground × Input (ctx b e) .ground :=
  if strict then strictPair (SourceMachineConjunctionPlan.plan b e) else weakDAG b e

end LogicLineages.ControlSensitivityCurrent.CurrentControlHardness
