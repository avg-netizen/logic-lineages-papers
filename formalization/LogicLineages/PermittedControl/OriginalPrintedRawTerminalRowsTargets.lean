module
public import LogicLineages.PermittedControl.OriginalPlainTerminalMatrixTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawTerminalRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (RawRow TestCode encodeRow)
open MixedSameRankResidue (WeightedCode)

def weightedCode (t : Int × NormalForm.Code.ItemData) : WeightedCode :=
  (t.1,(0,t.2.2.1,(0,0,0,0)))

def testCode (kind modulus : Nat) : TestCode :=
  if kind = 0 then (1,0) else (3,modulus + 1)

def atomCode (atom : NormalForm.Code.AtomData) : RawRow :=
  (testCode atom.1 atom.2.1,atom.2.2.1,atom.2.2.2.map weightedCode)

/-- Ordered raw encoding of the typed terminal projection. Genuine atom
positions, signed constants, all weights and literal names are preserved.
This is not admission of arithmetic outside the source plain domain. -/
def rowsCode (code : Nat) : List RawRow :=
  (LinearRows.Code.atoms code).map (fun a => atomCode (LinearRows.Code.decodeAtom a))

def ExactOriginalRawTerminalAtoms : Prop :=
  ∀ a : NormalForm.Atom,
    atomCode (LinearRows.Code.decodeAtom (Encodable.encode a.data)) =
      encodeRow (OriginalPlainTerminalMatrix.atomRow a)

def ExactOriginalRawTerminalRows : Prop :=
  ∀ p : NormalForm.Formula,
    rowsCode p.encode = (OriginalPlainTerminalMatrix.rows p).map encodeRow ∧
      (rowsCode p.encode).length = (LinearRows.atoms p).length

def ExactOriginalRawTerminalRowsEffectivity : Prop :=
  Primrec weightedCode ∧ Primrec atomCode ∧ Primrec rowsCode

def FullOriginalPrintedRawTerminalRows : Prop :=
  ExactOriginalRawTerminalAtoms ∧ ExactOriginalRawTerminalRows ∧
    ExactOriginalRawTerminalRowsEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawTerminalRows
