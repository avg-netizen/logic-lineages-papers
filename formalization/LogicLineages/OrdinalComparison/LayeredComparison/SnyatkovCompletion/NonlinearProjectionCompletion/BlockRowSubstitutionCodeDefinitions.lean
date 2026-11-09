module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCode

/-- Literal internal block-row data. Expanded terms and normal-form summands
keep their existing original encodings; occurrence entries are never collected. -/
abbrev EntryData := Int × NormalForm.Code.ItemData
abbrev RowData := (Nat × Nat) × List EntryData

def rowData (r : BlockRows.Row) : RowData :=
  ((r.1.1.encode, r.1.2.encode), r.2.map (fun a => (a.1, a.2.data)))

/-- Move exactly the selected raw-name occurrence into both signed parameter
codes, including zero/cancelled weights. Retained entries are byte-for-byte data. -/
def step (i replacement : Nat) (a : EntryData) (r : RowData) : RowData :=
  if a.2.2.1 = i then
    let term := WindowCode.termSubstitute i replacement (NormalForm.Code.itemTerm a.2)
    ((WindowCode.add (WindowCode.multiply a.1.toNat term) r.1.1,
      WindowCode.add (WindowCode.multiply (-a.1).toNat term) r.1.2), r.2)
  else (r.1, a :: r.2)

def entries (i replacement positive negative : Nat) (es : List EntryData) : RowData :=
  es.foldr (step i replacement) ((positive, negative), [])

/-- Both original parameter terms undergo the same actual substitution. -/
def row (i replacement : Nat) (r : RowData) : RowData :=
  entries i replacement (WindowCode.termSubstitute i replacement r.1.1)
    (WindowCode.termSubstitute i replacement r.1.2) r.2

def decodeRow (code : Nat) : RowData :=
  (Encodable.decode code).getD ((0, 0), [])

/-- A total all-code wrapper with an explicit fixed malformed-payload fallback.
Calibration is against genuine rowData, not an assumed syntax-validity oracle. -/
def encoded (i replacement code : Nat) : Nat :=
  Encodable.encode (row i replacement (decodeRow code))

abbrev EntryInput := Nat × (Nat × (Nat × (Nat × List EntryData)))
abbrev RowInput := Nat × (Nat × RowData)
abbrev EncodedInput := Nat × (Nat × Nat)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCode
