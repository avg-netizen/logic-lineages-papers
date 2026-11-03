module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent
open BalancedSyntax
open CommonHeadCompiler (Instruction)

abbrev Lower (Γ : List Nat) := Syntax Γ → Syntax Γ → Int → BaseFormula.Formula
abbrev Code := List Instruction
abbrev Call (Γ : List Nat) := Syntax Γ × Syntax Γ × Int
abbrev Input := List Nat × Nat × Nat × Nat × Int

/-- Correctness is an explicit induction premise, only for genuine lower
terms and positivity on THEIR actual pair support. The certificate and raw
valuation are fixed and shared; no values outside that support are restricted. -/
def LowerCorrect (Γ : List Nat) (C : Certificate Γ) (lower : Lower Γ)
    (ν : Nat → Nat) : Prop :=
  ∀ (E F : Syntax Γ) (desired : Int),
    genuineExpression Γ E → genuineExpression Γ F →
    (∀ i ∈ rawVariables Γ C E ++ rawVariables Γ C F, 0 < ν i) →
    ((lower E F desired).eval ν ↔
      Int.sign ((value Γ C E ν : Int) - (value Γ C F ν : Int)) = desired)

/-- A separate structural premise, not inferred from semantic correctness.
It is independent of genuineness and the valuation. -/
def LowerSupport (Γ : List Nat) (C : Certificate Γ) (lower : Lower Γ) : Prop :=
  ∀ (E F : Syntax Γ) (desired : Int), ∀ i ∈ (lower E F desired).variables,
    i ∈ rawVariables Γ C E ++ rawVariables Γ C F

def label (Γ : List Nat) (labels : List (Syntax Γ)) (i : Nat) : Syntax Γ :=
  labels.getD i (Affine.numeral Γ 0)

def labelSupport (Γ : List Nat) (C : Certificate Γ)
    (labels : List (Syntax Γ)) : List Nat :=
  labels.flatMap (rawVariables Γ C)

noncomputable def labelValuation (Γ : List Nat) (C : Certificate Γ)
    (labels : List (Syntax Γ)) (ν : Nat → Nat) (i : Nat) : Nat :=
  value Γ C (label Γ labels i) ν

/-- Labels already denote complete norm inputs. A bound c ≤ label i is
exactly NOT (label i < the actual lower-source numeral c). No head norm is
subtracted, no threshold is enlarged, and even a zero bound retains negation. -/
def translateGuard (Γ : List Nat) (lower : Lower Γ) (labels : List (Syntax Γ)) :
    CommonHeadLargeGuards.Formula → BaseFormula.Formula
  | .truth => .truth
  | .falsity => .falsity
  | .eq i j => lower (label Γ labels i) (label Γ labels j) 0
  | .lt i j => lower (label Γ labels i) (label Γ labels j) (-1)
  | .bound c i => .negative (lower (label Γ labels i) (Affine.numeral Γ c) (-1))
  | .neg p => .negative (translateGuard Γ lower labels p)
  | .conj p q => .conjunction (translateGuard Γ lower labels p)
      (translateGuard Γ lower labels q)
  | .disj p q => .disjunction (translateGuard Γ lower labels p)
      (translateGuard Γ lower labels q)

noncomputable def sourceTranslation (k : Nat) (Γ : List Nat)
    (C : Certificate (k :: Γ)) (E F : Upper k) (desired : Int)
    (lower : Lower Γ) : BaseFormula.Formula :=
  translateGuard Γ lower (BalancedLargeGuards.sourceTerms k Γ C E F)
    (BalancedLargeGuards.sourceFormula E F desired)

/-- One actual typed call per ORIGINAL postfix instruction. Boolean
instructions get a harmless 0=0 call whose result assembly ignores. -/
def typedChild (Γ : List Nat) (labels : List (Syntax Γ)) (q : Instruction) : Call Γ :=
  if q.1 = 2 then (label Γ labels q.2.1, label Γ labels q.2.2, 0)
  else if q.1 = 3 then (label Γ labels q.2.1, label Γ labels q.2.2, -1)
  else if q.1 = 4 then (label Γ labels q.2.2, Affine.numeral Γ q.2.1, -1)
  else (Affine.numeral Γ 0, Affine.numeral Γ 0, 0)

def encodeCall (Γ : List Nat) (C : Certificate Γ) (a : Call Γ) : Input :=
  (Γ, BalancedEvaluation.encodeCertificate Γ C,
    BalancedEvaluation.encodeSyntax Γ a.1, BalancedEvaluation.encodeSyntax Γ a.2.1, a.2.2)

/-- Literal encodings of the supplied typed comparator's results. No raw
decoder or numerical comparator oracle is being defined or assumed correct. -/
def typedResults (Γ : List Nat) (lower : Lower Γ) (labels : List (Syntax Γ))
    (code : Code) : List Code :=
  code.map (fun q =>
    let a := typedChild Γ labels q
    (lower a.1 a.2.1 a.2.2).encode)

def labelCode (Γ : List Nat) (labels : List Nat) (i : Nat) : Nat :=
  labels.getD i (BalancedAffineCode.numeral Γ 0)

/-- Actual raw balanced-source encodings, including the original lower
certificate. The common-layer constantCode belongs to another source grammar
and is deliberately not used here. -/
def child (Γ : List Nat) (C : Nat) (labels : List Nat) (q : Instruction) : Input :=
  if q.1 = 2 then (Γ, C, labelCode Γ labels q.2.1, labelCode Γ labels q.2.2, 0)
  else if q.1 = 3 then (Γ, C, labelCode Γ labels q.2.1, labelCode Γ labels q.2.2, -1)
  else if q.1 = 4 then
    (Γ, C, labelCode Γ labels q.2.2, BalancedAffineCode.numeral Γ q.2.1, -1)
  else (Γ, C, BalancedAffineCode.numeral Γ 0, BalancedAffineCode.numeral Γ 0, 0)

def children (Γ : List Nat) (C : Nat) (labels : List Nat) (code : Code) : List Input :=
  code.map (child Γ C labels)

/-- Boolean commands are retained verbatim. Every bound instruction appends
negation to its child's exact result, including bound zero. -/
def instructionCode (q : Instruction) (result : Code) : Code :=
  if q.1 = 2 then result
  else if q.1 = 3 then result
  else if q.1 = 4 then result ++ [(5,0,0)]
  else [q]

def assemble (code : Code) (results : List Code) : Code :=
  (code.zipWith instructionCode results).flatten

noncomputable def sourceChildren (k : Nat) (Γ : List Nat) (C E F : Nat)
    (desired : Int) : List Input :=
  children Γ (BalancedSourceAdapter.lowerCertificate C)
    (BalancedSourceAdapter.termCodes k Γ C E F)
    (BalancedSourceAdapter.formulaCode k E F desired)

noncomputable def sourceAssemble (k E F : Nat) (desired : Int)
    (results : List Code) : Code :=
  assemble (BalancedSourceAdapter.formulaCode k E F desired) results

def measure (a : Input) : Nat := a.1.length

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent
