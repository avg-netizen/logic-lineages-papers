module

public import LogicLineages.PersistentMarking.NumberedWindowRootDispatchAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramTargets
open LogicLineages.ComputabilityKnowledge NumberedWindowRootDispatchAlgorithm List.Vector

abbrev Key := Nat × Nat × Nat
abbrev Args := Nat × Nat
abbrev Selection := Bool × Nat × List Nat × Nat × Nat

structure PrimitiveRules (rules : Rules) : Prop where
  mark : Primrec (fun p : Key => rules.mark p.1 p.2.1 p.2.2)
  lower : Primrec₂ rules.lower
  select : Primrec (fun p : Selection => rules.select p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  copy : Primrec₂ rules.copy
  stat : Primrec (fun p : Key => rules.stat p.1 p.2.1 p.2.2)
  fabs : Primrec₂ rules.fabs
  beta : Primrec₂ rules.beta
  bottom : Primrec₂ rules.bottom

def RootDispatchProgram : Prop := ∀ rules, PrimitiveRules rules →
  ∃ p : GorbowPRProgram.Program 3, ∀ q cert r,
    GorbowPRProgram.evaluate p (q ::ᵥ cert ::ᵥ r ::ᵥ List.Vector.nil) =
      (check rules q cert r).toNat

end LogicLineages.PersistentMarking.NumberedWindowRootDispatchProgramTargets
