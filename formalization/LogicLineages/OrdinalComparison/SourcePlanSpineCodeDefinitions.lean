module
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeDefinitions
public import LogicLineages.OrdinalComparison.ParametricExistentialPlanDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode
open ExistentialPlan PrimitiveLowering SourcePrimitiveForestCode

/-- Canonical list instruction: tag, then three natural payload slots.
Tags 0/1/2/3/4 are source equation/eq/add/one/existential.
Tag 5 represents unsupported sort; every other tag has the same inert default. -/
abbrev Instruction := Nat × (Nat × (Nat × Nat))
abbrev State := Nat × List (Nat × Nat)
def gateInstruction {Γ} : Gate Γ → Instruction
  | .eq a b => (1,portNumber a,portNumber b,0)
  | .add a b c => (2,portNumber a,portNumber b,portNumber c)
  | .one a => (3,portNumber a,0,0)
  | .sort _ _ _ _ => (5,0,0,0)
/-- Leaf payloads use actual unfolded source-term encoding, not a DAG node code. -/
def spine {Γ} : Plan Γ → List Instruction
  | .done => []
  | .equation a b q => (0,SyntaxCode.encodeTerm a.term,SyntaxCode.encodeTerm b.term,0)::spine q
  | .gate g q => gateInstruction g::spine q
  | .existsGround q => (4,0,0,0)::spine q

def step (i : Instruction) (s : State) : State :=
  let w := s.1
  let a := shiftPort w i.2.1
  let b := shiftPort w i.2.2.1
  let c := shiftPort w i.2.2.2
  if i.1=0 then (w,SourcePlanPrefixCode.shiftPair w (i.2.1,i.2.2.1)::s.2)
  else if i.1=1 then (9+w,eqForest a b ++ SourcePlanPrefixCode.shiftPairs 9 s.2)
  else if i.1=2 then (9+w,addForest a b c ++ SourcePlanPrefixCode.shiftPairs 9 s.2)
  else if i.1=3 then (9+w,oneForest a ++ SourcePlanPrefixCode.shiftPairs 9 s.2)
  else if i.1=4 then (1+w,s.2)
  else s

def run (is : List Instruction) : State := is.foldr step (0,[])
def aggregateCode (is : List Instruction) : Nat × Nat :=
  SourceGammaAggregateCode.aggregateCode (run is).2

def compiledPairs {Γ} (q : Plan Γ) : List (Nat × Nat) :=
  (compile q).forest.map (fun p => (SyntaxCode.encodeTerm p.1.term,SyntaxCode.encodeTerm p.2.term))
end LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode
