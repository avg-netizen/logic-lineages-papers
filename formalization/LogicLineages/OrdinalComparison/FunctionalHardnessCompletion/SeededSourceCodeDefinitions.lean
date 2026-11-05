module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SeededCompilerDefinitions
public import LogicLineages.OrdinalComparison.ContextInsertionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode
open OriginalDomain SignedPair FunctionalDetector

/-- The existing source codec, not a semantic or compressed replacement. -/
abbrev PairCode := Nat × Nat
abbrev State := PairCode × Nat

def pairCode {Γ : List Ty} (p : Pair Γ) : PairCode :=
  (SyntaxCode.encodeTerm p.1, SyntaxCode.encodeTerm p.2)

def appCode (f a : Nat) : Nat := 8 * Nat.pair f a + 5
def lamCode (type body : Nat) : Nat := 8 * Nat.pair type body + 6
def weakenCode (a : Nat) : Nat := ContextInsertionCode.sourceCode 0 1 a

def identityCode : Nat := lamCode 0 0

def combineCode (a b : Nat) : Nat :=
  appCode (lamCode (SyntaxCode.typeCode (.arrow .ground unary)) (weakenCode a))
    (lamCode 0 (weakenCode b))

def projectCode (a b : Nat) : Nat :=
  appCode (lamCode (SyntaxCode.typeCode unary) (weakenCode a)) b

def omegaCode (a : Nat) : Nat :=
  appCode (appCode 4 1) (lamCode 0 (weakenCode a))

def joinCode (p q : PairCode) : PairCode :=
  (combineCode p.1 q.1, combineCode p.2 q.2)
def eightCode (p : PairCode) : PairCode :=
  (combineCode p.1 identityCode, combineCode p.2 identityCode)
def sixteenCode (p : PairCode) : PairCode := joinCode p p

def padCode (d : Nat) (p : PairCode) : PairCode :=
  (sixteenCode^[d % 3]) ((eightCode^[d / 3 + (2 - d % 3)]) p)

/-- Fixed finite closed trees. These are literal source encodings, independent
of the free context. No invented source primitive or semantic value is encoded. -/
def unitCode : PairCode := pairCode (@unitPair [])
def seedCode : PairCode := pairCode (@OmegaSeed.pair [])

def variableCode (i : Nat) : PairCode :=
  joinCode ((eightCode^[3])
    (projectCode (8 * i) identityCode, projectCode identityCode identityCode)) unitCode

/-- A radix-six expression codec. All recursive child codes are strictly
smaller than the enclosing node. Tag five has a specified total default. -/
def expressionCode {n : Nat} : Expression n → Nat
  | .unit => 0
  | .var i => 6 * i.val + 1
  | .add a b => 6 * Nat.pair (expressionCode a) (expressionCode b) + 2
  | .neg a => 6 * expressionCode a + 3
  | .shift a => 6 * expressionCode a + 4

def negStep (s : State) : State := ((s.1.2, s.1.1), s.2)
def omegaStep (s : State) : State := ((omegaCode s.1.1, omegaCode s.1.2), s.2 + 1)
def addStep (s t : State) : State :=
  let k := max s.2 t.2
  (joinCode (padCode (k - s.2) s.1) (padCode (k - t.2) t.1), k + 9)

/-- A total numerical implementation of the ACTUAL seeded compiler. Only the
last typed index is a seed; malformed larger raw indices have the same harmless
closed default. Calibration is asserted on every typed input, not on bad codes. -/
def compilerCode (n : Nat) : Nat → State
  | e =>
    if e % 6 = 1 then
      if e / 6 < n then (variableCode (e / 6), 15) else (seedCode, 12)
    else if h : e % 6 = 2 ∨ e % 6 = 3 ∨ e % 6 = 4 then
      have hd : e / 6 < e := Nat.div_lt_self (by omega) (by decide)
      if e % 6 = 2 then
        have hl : (e / 6).unpair.1 < e := (Nat.unpair_left_le _).trans_lt hd
        have hr : (e / 6).unpair.2 < e := (Nat.unpair_right_le _).trans_lt hd
        addStep (compilerCode n (e / 6).unpair.1) (compilerCode n (e / 6).unpair.2)
      else if e % 6 = 3 then negStep (compilerCode n (e / 6))
      else omegaStep (compilerCode n (e / 6))
    else (unitCode, 12)
termination_by e => e
decreasing_by all_goals assumption

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededSourceCode
