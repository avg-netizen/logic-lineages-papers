module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockRowSubstitutionCodeDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCode

/-- Original atom tag and modulus-minus-one, with the accepted literal
block-row data. The row keeps both signed parameter terms and all occurrences. -/
abbrev AtomData := Nat × (Nat × BlockRowSubstitutionCode.RowData)

def atomData : BlockRows.Atom → AtomData
  | .nonnegative r => (0, 0, BlockRowSubstitutionCode.rowData r)
  | .divisible m r => (1, m, BlockRowSubstitutionCode.rowData r)

/-- Preserve the raw tag and modulus field exactly; run the SAME numeric row
substitution on the complete original row data, including malformed fields. -/
def atom (i replacement : Nat) (a : AtomData) : AtomData :=
  (a.1, a.2.1, BlockRowSubstitutionCode.row i replacement a.2.2)

/-- Explicit fixed malformed-payload fallback, without a validity oracle. -/
def decodeAtom (code : Nat) : AtomData :=
  (Encodable.decode code).getD (0, 0, ((0, 0), []))

def encodedAtom (i replacement code : Nat) : Nat :=
  Encodable.encode (atom i replacement (decodeAtom code))

/-- Literal radix-six encoding of the UNCHANGED original block formula.
Every Boolean occurrence and guarded atom remains at its original position. -/
def formulaCode : BlockRows.Formula → Nat
  | .truth => 0
  | .falsity => 1
  | .atom a => 6 * Encodable.encode (atomData a) + 2
  | .negative p => 6 * formulaCode p + 3
  | .conjunction p q => 6 * Nat.pair (formulaCode p) (formulaCode q) + 4
  | .disjunction p q => 6 * Nat.pair (formulaCode p) (formulaCode q) + 5

/-- The SAME inherited all-code Boolean map with this concrete payload
program. No typed decoder or assumed syntax-computation interface is used. -/
def formula (i replacement code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (encodedAtom i replacement) code

abbrev AtomInput := Nat × (Nat × AtomData)
abbrev CodeInput := Nat × (Nat × Nat)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCode
