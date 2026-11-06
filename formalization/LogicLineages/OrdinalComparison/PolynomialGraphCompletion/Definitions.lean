module
public import LogicLineages.OrdinalComparison.KernelSourceCompletion.UniformCompletion.Definitions
public import LogicLineages.OrdinalComparison.PeakWordProgramDefinitions
public import LogicLineages.OrdinalComparison.PrincipalWordActionDefinitions
public import LogicLineages.OrdinalComparison.ActualCollapseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.PolynomialGraphCompletion
open KernelSourceCompletion KernelSourceCompletion.UniformCompletion

/-- Numeric word syntax. Tags 0,1,2,3,4 are respectively signed shift,
Phi, V, X and E. The remaining fields are degree, retained mass and index.
Unused fields do not change the denoted source symbol. -/
abbrev Letter := Nat × Nat × Nat × Int
abbrev Word := List Letter
abbrev Call := Nat × Nat
abbrev UnaryRow := Int × List (Int × Word)
abbrev Row := Int × List (Int × (Nat × Word))

def shiftLetter (j : Int) : Letter := (0,0,0,j)
def phiLetter : Letter := (1,0,0,0)
def quadraticLetter (j : Int) : Letter := (2,0,0,j)
def kernelLetter (d c : Nat) (j : Int) : Letter := (3,d,c,j)
def counterLetter (d c : Nat) : Letter := (4,d,c,0)

def LetterAllowed (D : Nat) (a : Letter) : Prop :=
  if a.1 ≤ 2 then True else
    (a.1 = 3 ∨ a.1 = 4) ∧ 3 ≤ a.2.1 ∧ a.2.1 ≤ D

/-- Source semantics, including the independently scheduled X/E functions.
Raw total extensions receive source meaning only on LetterDomain below. -/
noncomputable def letterValue (a : Letter) (t : Nat) : Nat :=
  if a.1 = 0 then ((t : Int) + a.2.2.2).toNat
  else if a.1 = 1 then Phi t
  else if a.1 = 2 then rawQuadraticShift a.2.2.2 t
  else if a.1 = 3 then sourceSignedValue a.2.1 a.2.2.1 a.2.2.2 t
  else sourceCount a.2.1 a.2.2.1 t

noncomputable def LetterDomain (a : Letter) (t : Nat) : Prop :=
  if a.1 = 0 then 0 ≤ (t : Int) + a.2.2.2
  else if a.1 = 1 then True
  else if a.1 = 2 then 0 < ((Phi t / 2 : Nat) : Int) + a.2.2.2 + 1
  else if a.1 = 3 then a.2.2.1 ≤ Phi t ∧
    0 < sourceSignedDepth a.2.1 a.2.2.1 a.2.2.2 t
  else a.1 = 4 ∧ a.2.2.1 ≤ Phi t

noncomputable def wordValue : Word → Nat → Nat
  | [], t => t
  | a :: w, t => wordValue w (letterValue a t)

noncomputable def WordDomain : Word → Nat → Prop
  | [], _ => True
  | a :: w, t => LetterDomain a t ∧ WordDomain w (letterValue a t)

def WordAllowed (D : Nat) (w : Word) : Prop := ∀ a ∈ w, LetterAllowed D a

noncomputable def unaryValue (r : UnaryRow) (t : Nat) : Int :=
  r.1 + (r.2.map (fun a => a.1 * (wordValue a.2 t : Int))).sum
noncomputable def UnaryDomain (r : UnaryRow) (t : Nat) : Prop :=
  ∀ a ∈ r.2, WordDomain a.2 t
def UnaryAllowed (D : Nat) (r : UnaryRow) : Prop :=
  ∀ a ∈ r.2, WordAllowed D a.2

noncomputable def RowValue (r : Row) (ν : Nat → Nat) : Int :=
  r.1 + (r.2.map (fun a => a.1 * (wordValue a.2.2 (ν a.2.1) : Int))).sum
noncomputable def RowDomain (r : Row) (ν : Nat → Nat) : Prop :=
  ∀ a ∈ r.2, WordDomain a.2.2 (ν a.2.1)
def RowAllowed (D : Nat) (r : Row) : Prop :=
  ∀ a ∈ r.2, WordAllowed D a.2.2
def rowVariables (r : Row) : List Nat := r.2.map (fun a => a.2.1)

def addUnary (r s : UnaryRow) : UnaryRow := (r.1+s.1,r.2++s.2)
def prepend (w : Word) (r : UnaryRow) : UnaryRow :=
  (r.1,r.2.map (fun a => (a.1,w++a.2)))

def rangeLetter (p : Call) : Letter :=
  if p.1 = 1 then phiLetter
  else if p.1 = 2 then quadraticLetter (-(((p.2+1)/2 : Nat) : Int))
  else kernelLetter p.1 p.2 0

def countContribution (p : Call) : UnaryRow :=
  if p.1 = 1 then (2,[])
  else if p.1 = 2 then
    (2-2*(((p.2+1)/2 : Nat) : Int),[(1,[phiLetter])])
  else (0,[(2,[counterLetter p.1 p.2])])

/-- Compile only unary composition and integer-linear rows. No source
function is ever applied to a sum of row values. -/
def compileCalls (calls : List Call) : UnaryRow :=
  calls.foldr (fun p r => addUnary (countContribution p) (prepend [rangeLetter p] r))
    (0,[(2,[])])

noncomputable def callRun : List Call → Nat → Nat × Nat
  | [], t => (t,0)
  | p :: ps, t =>
      let z := actualSuffixKernel (Ordinal.omega0 ^ (p.1 : Ordinal)) p.2 t
      let out := callRun ps z
      (out.1,actualSuffixKernelCount (Ordinal.omega0 ^ (p.1 : Ordinal)) p.2 t + out.2)

noncomputable def CallsGenuine : List Call → Nat → Prop
  | [], _ => True
  | p :: ps, t => p.2+p.1+1 ≤ t ∧
      CallsGenuine ps (actualSuffixKernel (Ordinal.omega0 ^ (p.1 : Ordinal)) p.2 t)

def headCalls (code : Nat) : List Call :=
  (encodedPrincipalPeakWord code).map (fun p => (rawNormCode p.1,p.2))
def headRow (code : Nat) : UnaryRow :=
  prepend [shiftLetter (rawNormCode code : Int)] (compileCalls (headCalls code))
def headDegree (code : Nat) : Nat := 3 + rawNormCode code
def familyDegree (codes : List Nat) : Nat := 3 + (codes.map rawNormCode).sum

noncomputable def ValidHead (code : Nat) : Prop :=
  ONote.NF (rawNoteDecode code) ∧ Order.IsSuccLimit (rawNoteDecode code).repr ∧
    (rawNoteDecode code).repr < Ordinal.omega0 ^ Ordinal.omega0

noncomputable def headValue (code n : Nat) : Nat :=
  actualCollapse ((rawNoteDecode code).repr + (n : Ordinal))

/-- The generated graphs have proved domains on the whole natural input
domain. Their literal finite-exception table is consequently empty. -/
def graphCutoff (_ : Nat) : Nat := 0
def graphExceptions (_ : Nat) : List (Nat × Nat) := []
noncomputable def HeadGraph (code n y : Nat) : Prop :=
  (graphCutoff code ≤ n ∧ UnaryDomain (headRow code) n ∧
    2*(y : Int) = unaryValue (headRow code) n) ∨
  ∃ p ∈ graphExceptions code, n = p.1 ∧ y = p.2

/-- A literal word-linear equality with symbolic input and output names. -/
def headEquation (code input output : Nat) : Row :=
  (-(headRow code).1, (2,output,[]) ::
    (headRow code).2.map (fun a => (-a.1,input,a.2)))

end LogicLineages.OrdinalComparison.PolynomialGraphCompletion
