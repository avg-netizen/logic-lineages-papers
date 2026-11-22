module
public import LogicLineages.PermittedControl.OriginalPrintedRawPositionalTerminalTargets
public import LogicLineages.PermittedControl.OriginalPrintedTerminalBitClausesTargets
public import LogicLineages.PermittedControl.ActualBitFamilyRawLayoutTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawClauseAssembly
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (Row RawRow encodeRow)
open ActualBitFamilyRawLayout (RawBitRow RawFamily encodeFamily)
open OriginalPrintedTerminalBitClauses (vectors accepted clauses)
open OriginalPrintedRawPositionalTerminal (finishCode)

abbrev ChoiceArgs := Nat × Bool × Nat
abbrev Args := Nat × Bool × List RawRow × List RawRow

def acceptedCode (p : ChoiceArgs) : List (List Bool) :=
  (vectors p.2.2).filter (fun bits => decide (finishCode (p.1,bits) = some p.2.1))

/-- This is assembly of two *supplied* row tapes, not graph emission.
All graph rows are literally positive and only the ordered suffix tracks
the terminal vector and chosen polarity. -/
def clausesCode (p : Args) : RawFamily :=
  (acceptedCode (p.1,p.2.1,p.2.2.2.length)).map (fun bits =>
    p.2.2.1.map (fun row => (row,true)) ++ p.2.2.2.zip bits)

def ExactOriginalRawAcceptedChoices : Prop :=
  (∀ (p : NormalForm.Formula) (polarity : Bool) (n : Nat),
    acceptedCode (p.encode,polarity,n) = accepted p polarity n) ∧
  ∀ (p : ChoiceArgs) (bits : List Bool), bits ∈ acceptedCode p ↔
    bits.length = p.2.2 ∧ finishCode (p.1,bits) = some p.2.1

def ExactOriginalRawClauseAssembly : Prop :=
  ∀ (pre tail : List Row) (p : NormalForm.Formula) (polarity : Bool),
    clausesCode (p.encode,polarity,pre.map encodeRow,tail.map encodeRow) =
      encodeFamily (clauses pre tail p polarity)

def ExactOriginalRawClausePositions : Prop :=
  ∀ (p : Args) (branch : List RawBitRow), branch ∈ clausesCode p →
    let pre := p.2.2.1
    let tail := p.2.2.2
    ∃ bits ∈ acceptedCode (p.1,p.2.1,tail.length),
      branch.take pre.length = pre.map (fun row => (row,true)) ∧
      branch.drop pre.length = tail.zip bits ∧ branch.length = pre.length + tail.length

def ExactOriginalRawClauseEffectivity : Prop :=
  Primrec vectors ∧ Primrec acceptedCode ∧ Primrec clausesCode

def FullOriginalPrintedRawClauseAssembly : Prop :=
  ExactOriginalRawAcceptedChoices ∧ ExactOriginalRawClauseAssembly ∧
    ExactOriginalRawClausePositions ∧ ExactOriginalRawClauseEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawClauseAssembly
