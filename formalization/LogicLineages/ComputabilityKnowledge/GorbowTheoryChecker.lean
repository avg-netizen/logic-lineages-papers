module

public import LogicLineages.ComputabilityKnowledge.GorbowTheoryProof
public import LogicLineages.ComputabilityKnowledge.GorbowProofChecker

@[expose] public section
/-! Concrete annotated proof checking with an explicit external axiom program.
Only canonical rule4 adds literal parsed closed axioms; old rules0--3 are
unchanged. No particular Base/DCB program or represented provability is asserted. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowTheoryChecker
open GorbowSyntax GorbowTheoryProof GorbowProofChecker

def ProgramTheory (axCheck : List Nat → Bool) (σ : Sentence) : Prop :=
  axCheck (GorbowFormulaPrefixCode.encode σ)=true

def axiomCheck (axCheck : List Nat → Bool) (n : Nat) (raw : List Nat) (p : Payload) : Bool :=
  decide (p.1=0 ∧ p.2.1.length=1 ∧ p.2.2.1=0 ∧ p.2.2.2=0 ∧
    GorbowSyntaxValidation.validFormula 0 (p.2.1.getD 0 [])=true ∧
    axCheck (p.2.1.getD 0 [])=true ∧
    GorbowSubstitutionCode.substituteFormulaCode 0 n [] (p.2.1.getD 0 [])=some raw)

def ruleCheck (axCheck : List Nat → Bool) (history : History) (line : Line) : Bool :=
  if rule line=4 then axiomCheck axCheck (context line) (conclusion line) (payload line)
  else GorbowProofChecker.ruleCheck history line

def lineCheck (axCheck : List Nat → Bool) (history : History) (line : Line) : Bool :=
  GorbowSyntaxValidation.validFormula (context line) (conclusion line) && ruleCheck axCheck history line

def step (axCheck : List Nat → Bool) (state : Option History) (line : Line) : Option History := do
  let history ← state
  if lineCheck axCheck history line then some ((context line,conclusion line)::history) else none

def run (axCheck : List Nat → Bool) (history : History) (lines : List Line) : Option History :=
  lines.foldl (step axCheck) (some history)
def checkProof (axCheck : List Nat → Bool) (lines : List Line) : Option History := run axCheck [] lines

def verifies (axCheck : List Nat → Bool) (n : Nat) (raw : List Nat) (lines : List Line) : Bool :=
  match checkProof axCheck lines with
  | some ((m,out)::_) => decide (n=m ∧ raw=out)
  | _ => false

def axiomLine (n : Nat) (σ : Sentence) : Line :=
  (n,GorbowFormulaPrefixCode.encode (weakenClosed n σ),4,0,[GorbowFormulaPrefixCode.encode σ],0,0)

def proofLines (axCheck : List Nat → Bool) : {n : Nat} → {φ : Formula n} → Derivation (ProgramTheory axCheck) φ → List Line
  | _,_,.logical w => [logicalLine w]
  | _,_,.arithmetic w => [arithmeticLine w]
  | n,_,.axiom σ _ => [axiomLine n σ]
  | n,φ,.mp p q => proofLines axCheck p ++ proofLines axCheck q ++ [mpLine n (GorbowFormulaPrefixCode.encode φ) (proofLines axCheck q).length 0]
  | n,_,.generalize (a:=φ) p => proofLines axCheck p ++ [generalizeLine n (GorbowFormulaPrefixCode.encode (.all φ)) 0]

def SoundHistory (axCheck : List Nat → Bool) (history : History) : Prop := ∀ entry ∈ history,
  ∃ φ : Formula entry.1, entry.2=GorbowFormulaPrefixCode.encode φ ∧ Nonempty (Derivation (ProgramTheory axCheck) φ)
end LogicLineages.ComputabilityKnowledge.GorbowTheoryChecker
