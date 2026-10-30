module

public import LogicLineages.ComputabilityKnowledge.PredictionRawMachineDefinitions
public import LogicLineages.ComputabilityKnowledge.PredictionCodeEvaderDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionRawTrace
open PredictionRawMachine

/-- Structural bound on input pops within one finite statement. Branch uses
maximum, so this is a bound, not a claimed exact dynamic pop counter. -/
def inputPopBound {k : Nat} : Stmt k → Nat
  | .push _ _ q => inputPopBound q
  | .peek _ _ q => inputPopBound q
  | .pop b _ q => (if b = false then 1 else 0) + inputPopBound q
  | .load _ q => inputPopBound q
  | .branch _ p q => max (inputPopBound p) (inputPopBound q)
  | .goto _ => 0
  | .halt => 0

def configurationPopBound {k : Nat} (c : Cfg k) : Nat :=
  match c.l with
  | none => 0
  | some i => inputPopBound (evaderStmt k i)

/-- Every edge is an actual raw TM2 step. Counters record transitions and the
sum of structural per-block pop bounds; neither is identified with tape time. -/
inductive CostedRun (k : Nat) : Cfg k → Cfg k → Nat → Nat → Prop
  | refl (c : Cfg k) : CostedRun k c c 0 0
  | step {c c' d : Cfg k} {n p : Nat} :
      machineStep k c = some c' → CostedRun k c' d n p →
      CostedRun k c d (n + 1) (configurationPopBound c + p)

end LogicLineages.ComputabilityKnowledge.PredictionRawTrace
