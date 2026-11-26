module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCode

@[expose] public section

/-! Concrete finite certificates for the explicitly specified PA core only.
Histories are newest-first, so every successful getElem? reference is strictly
earlier. Unused fields are canonical. No definitional U/u or arithmetical
representability claim is included in this external proof-checking algorithm. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowProofChecker
open GorbowSyntax GorbowPACore GorbowCodeConstructors GorbowSyntaxValidation
abbrev Payload := Nat × List (List Nat) × Nat × Nat
abbrev Line := Nat × List Nat × Nat × Payload
abbrev Entry := Nat × List Nat
abbrev History := List Entry

def context (line : Line) : Nat := line.1
def conclusion (line : Line) : List Nat := line.2.1
def rule (line : Line) : Nat := line.2.2.1
def payload (line : Line) : Payload := line.2.2.2

def ruleCheck (history : History) (line : Line) : Bool :=
  let n := context line
  let raw := conclusion line
  let p := payload line
  if rule line = 0 then decide (p.2.2.1 = 0 ∧ p.2.2.2 = 0 ∧ GorbowLogicalAxiomCode.compile n (p.1,p.2.1) = some raw)
  else if rule line = 1 then decide (p.2.2.1 = 0 ∧ p.2.2.2 = 0 ∧ GorbowArithmeticAxiomCode.compile n (p.1,p.2.1) = some raw)
  else if rule line = 2 then
    if p.1 = 0 ∧ p.2.1 = [] then
      match history[p.2.2.1]?, history[p.2.2.2]? with
      | some a, some b => decide (a.1 = n ∧ b.1 = n ∧ a.2 = binary 7 b.2 raw)
      | _, _ => false
    else false
  else if rule line = 3 then
    if p.1 = 0 ∧ p.2.1 = [] ∧ p.2.2.2 = 0 then
      match history[p.2.2.1]? with
      | some a => decide (a.1 = n+1 ∧ raw = unary 10 a.2)
      | _ => false
    else false
  else false

def lineCheck (history : History) (line : Line) : Bool :=
  validFormula (context line) (conclusion line) && ruleCheck history line

def step (state : Option History) (line : Line) : Option History := do
  let history ← state
  if lineCheck history line then some ((context line,conclusion line)::history) else none

def run (history : History) (lines : List Line) : Option History := lines.foldl step (some history)
def checkProof (lines : List Line) : Option History := run [] lines

def verifies (n : Nat) (raw : List Nat) (lines : List Line) : Bool :=
  match checkProof lines with
  | some ((m,out)::_) => decide (n=m ∧ raw=out)
  | _ => false

def logicalLine {n : Nat} (w : LogicalInstance n) : Line :=
  (n,GorbowFormulaPrefixCode.encode (logicalFormula w),0,(GorbowLogicalAxiomCode.encode w).1,(GorbowLogicalAxiomCode.encode w).2,0,0)
def arithmeticLine {n : Nat} (w : ArithmeticInstance n) : Line :=
  (n,GorbowFormulaPrefixCode.encode (arithmeticFormula w),1,(GorbowArithmeticAxiomCode.encode w).1,(GorbowArithmeticAxiomCode.encode w).2,0,0)
def mpLine (n : Nat) (raw : List Nat) (r1 r2 : Nat) : Line := (n,raw,2,0,[],r1,r2)
def generalizeLine (n : Nat) (raw : List Nat) (r : Nat) : Line := (n,raw,3,0,[],r,0)

def proofLines : {n : Nat} → {φ : Formula n} → Proof φ → List Line
  | _, _, .logical w => [logicalLine w]
  | _, _, .arithmetic w => [arithmeticLine w]
  | n, φ, .mp p q => proofLines p ++ proofLines q ++ [mpLine n (GorbowFormulaPrefixCode.encode φ) (proofLines q).length 0]
  | n, _, .generalize (a := φ) p => proofLines p ++ [generalizeLine n (GorbowFormulaPrefixCode.encode (.all φ)) 0]

def lineConclusions (lines : List Line) : History :=
  lines.reverse.map (fun line => (context line,conclusion line))

def SoundHistory (history : History) : Prop := ∀ entry ∈ history,
  ∃ φ : Formula entry.1, entry.2 = GorbowFormulaPrefixCode.encode φ ∧ Nonempty (Proof φ)
end LogicLineages.ComputabilityKnowledge.GorbowProofChecker
