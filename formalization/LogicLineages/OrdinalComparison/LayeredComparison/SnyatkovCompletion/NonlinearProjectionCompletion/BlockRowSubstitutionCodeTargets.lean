module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeTargets
open BlockRowSubstitutionCode

def LiteralEntryCalibration : Prop := ∀ (i : Nat) (replacement positive negative : Term)
    (es : List (Int × NormalForm.Summand)),
  entries i replacement.encode positive.encode negative.encode
    (es.map (fun a => (a.1, a.2.data))) =
      rowData (BlockRows.substituteEntries i replacement positive negative es)

def LiteralRowCalibration : Prop := ∀ (i : Nat) (replacement : Term) (r : BlockRows.Row),
  row i replacement.encode (rowData r) = rowData (r.substitute i replacement)

/-- One program with every name, code, initial parameter and list as runtime data.
No fixed-parameter family or primitive-recursive strengthening is asserted. -/
def ActualEntryProgram : Prop := Computable (fun p : EntryInput =>
  entries p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)

def ActualRowProgram : Prop := Computable (fun p : RowInput => row p.1 p.2.1 p.2.2)

def LiteralEncodedCalibration : Prop := ∀ (i : Nat) (replacement : Term) (r : BlockRows.Row),
  encoded i replacement.encode (Encodable.encode (rowData r)) =
    Encodable.encode (rowData (r.substitute i replacement))

def ActualEncodedProgram : Prop :=
  Computable (fun p : EncodedInput => encoded p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeTargets
