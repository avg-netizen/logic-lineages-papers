module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCode

abbrev EntryData := BlockRowSubstitutionCode.EntryData
abbrev RowData := BlockRowSubstitutionCode.RowData
abbrev AtomData := BlockFormulaSubstitutionCode.AtomData

/-- Literal numeric initializer step. Keep precisely the bound-name
occurrences; move every other occurrence into both signed parameter codes,
including zero weights. No term valuation or syntax-validity oracle is read. -/
def step (bound : List Nat) (a : EntryData) (r : RowData) : RowData :=
  if bound.contains a.2.2.1 then (r.1, a :: r.2) else
    ((WindowCode.add (WindowCode.multiply a.1.toNat (NormalForm.Code.itemTerm a.2)) r.1.1,
      WindowCode.add (WindowCode.multiply (-a.1).toNat (NormalForm.Code.itemTerm a.2)) r.1.2),
      r.2)

def entries (bound : List Nat) (positive negative : Nat) (es : List EntryData) : RowData :=
  es.foldr (step bound) ((positive, negative), [])

/-- The original integer constant becomes the same two natural numeral codes. -/
def row (bound : List Nat) (r : NormalForm.Code.RowData) : RowData :=
  entries bound (WindowCode.numeral r.1.toNat) (WindowCode.numeral (-r.1).toNat) r.2

/-- Raw source tag and modulus fields are preserved literally. -/
def atom (bound : List Nat) (a : NormalForm.Code.AtomData) : AtomData :=
  (a.1, a.2.1, row bound a.2.2)

/-- The same fixed source-payload fallback as the inherited normal-form codec. -/
def decodeAtom (code : Nat) : NormalForm.Code.AtomData :=
  (Encodable.decode code).getD (0, 0, (0 : Int), [])

def encodedAtom (bound : List Nat) (code : Nat) : Nat :=
  Encodable.encode (atom bound (decodeAtom code))

/-- Actual all-code initializer using the unchanged radix-six traversal.
The bound list and the entire source formula code are runtime inputs. -/
def formula (bound : List Nat) (code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (encodedAtom bound) code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitializationCode
