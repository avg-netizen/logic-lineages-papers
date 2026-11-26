module
public import LogicLineages.PermittedControl.OriginalPrintedRawGraphRowsTargets
public import LogicLineages.PermittedControl.OriginalPrintedRawTerminalRowsTargets
public import LogicLineages.PermittedControl.OriginalPrintedRawClauseAssemblyTargets
public import LogicLineages.PermittedControl.OriginalPrintedTypedExistentialTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontend
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open HeterogeneousSignedMatrixSlice (RawRow)
open OriginalPrintedRawGraphAllocator (OriginalArgs)
open OriginalPrintedCircuitSequential (Gate)
open OriginalPrintedCircuitNumericRead (encodeGate)
open ActualBitFamilyRawLayout (RawFamily encodeFamily)
open OriginalPrintedTypedExistential (literalFamily)

abbrev Args := OriginalArgs × Bool

def encodeInput (known : List Nat) (gs : List Gate) (p : NormalForm.Formula)
    (positive : Bool) : Args :=
  ((known,p.encode,gs.map encodeGate),positive)

def finish (p : Args) (pre : List RawRow) : RawFamily :=
  OriginalPrintedRawClauseAssembly.clausesCode
    (p.1.2.1,p.2,pre,OriginalPrintedRawTerminalRows.rowsCode p.1.2.1)

/-- Compile the literal surface matrix, retaining graph-emitter failure.
Success only authenticates genuine encodings under the calibration below. -/
def familyCode (p : Args) : Option RawFamily :=
  (OriginalPrintedRawGraphRows.rowsCode p.1).map (finish p)

def ExactOriginalRawFamilyFrontend : Prop :=
  ∀ (known : List Nat) (gs : List Gate) (p : NormalForm.Formula) (positive : Bool),
    familyCode (encodeInput known gs p positive) =
      some (encodeFamily (literalFamily known gs p positive))

def OriginalRawFamilyFrontendEffectivity : Prop := Primrec familyCode

def FullOriginalRawFamilyFrontend : Prop :=
  ExactOriginalRawFamilyFrontend ∧ OriginalRawFamilyFrontendEffectivity

end LogicLineages.PermittedControl.OriginalPrintedRawFamilyFrontend
