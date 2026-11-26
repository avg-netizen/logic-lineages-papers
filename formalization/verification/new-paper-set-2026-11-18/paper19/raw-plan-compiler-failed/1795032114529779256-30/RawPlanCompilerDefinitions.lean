module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingDefinitions
public import LogicLineages.ControlSensitivityCurrent.RawPrimitiveGateTargets
public import LogicLineages.OrdinalComparison.SourceExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler

open LogicLineages.OrdinalComparison.Source ExistentialPlan GroundEquivalence
open PrimitiveGate (GateCode encodeGate blockContext)

abbrev ForestCode := List (Code × Code)
abbrev Instruction := (Code × Code) ⊕ (GateCode ⊕ PUnit)
abbrev ResultCode := List Nat × List Nat × ForestCode
abbrev State := List Nat × ResultCode

def encodePlan {Γ : List Ty} : Plan Γ → List Instruction
  | .done => []
  | .equation a b tail => .inl (encode ⟨Γ,.ground,a⟩, encode ⟨Γ,.ground,b⟩) :: encodePlan tail
  | .gate g tail => .inr (.inl (encodeGate g)) :: encodePlan tail
  | .existsGround tail => .inr (.inr PUnit.unit) :: encodePlan tail

def encodeResult {Γ : List Ty} (r : Result Γ) : ResultCode :=
  (r.context.map SyntaxCode.typeCode, Operations.renamingCode r.embedding,
    RawPrimitiveGateTargets.encodeForest r.forest)

def pushContext (context : List Nat) (i : Instruction) : List Nat :=
  match i with
  | .inr (.inr _) => 0 :: context
  | _ => context

def endContext (context : List Nat) (code : List Instruction) : List Nat :=
  code.foldl pushContext context

def renamePortRaw (table : List Nat) (p : Nat) : Nat :=
  if p = 0 then 0 else table.getD (p - 1) 0 + 1

def renameGateRaw (table : List Nat) (g : GateCode) : GateCode :=
  let (tag,a,b,c,d) := g
  (tag, renamePortRaw table a, renamePortRaw table b, renamePortRaw table c, renamePortRaw table d)

def shiftTable (context : List Nat) : List Nat :=
  (List.range context.length).map (fun i => i + 9)

def shiftForest (context : List Nat) (fs : ForestCode) : ForestCode :=
  let table := shiftTable context
  let ctx := blockContext context
  fs.map fun e => (Operations.renameCode ctx table e.1, Operations.renameCode ctx table e.2)

def equationGuard (context : List Nat) (a b : Code) : Bool :=
  decide (a.1 = context ∧ b.1 = context ∧ a.2.2.2 = 0 ∧ b.2.2.2 = 0)

def compileStep (i : Instruction) (s : State) : Option State :=
  let (source, context, embedding, equations) := s
  match i with
  | .inl (a,b) => do
      if !equationGuard source a b then none else
        let a' ← CheckedRenaming.rename context embedding a
        let b' ← CheckedRenaming.rename context embedding b
        return (source, context, embedding, (a',b') :: equations)
  | .inr (.inl g) => do
      if !PrimitiveGate.gateGuard source g then none else
        let fresh ← PrimitiveGate.compile context (renameGateRaw embedding g)
        return (source, blockContext context, embedding.map (fun i => i + 9),
          fresh ++ shiftForest context equations)
  | .inr (.inr _) =>
      match source with
      | 0 :: tail => some (tail, context, embedding.tail, equations)
      | _ => none

def runState (context : List Nat) (code : List Instruction) : Option State :=
  let final := endContext context code
  code.foldr (fun i s => s.bind (compileStep i))
    (some (final, final, List.range final.length, []))

def run (context : List Nat) (code : List Instruction) : Option ResultCode :=
  (runState context code).map Prod.snd

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.PlanCompiler
