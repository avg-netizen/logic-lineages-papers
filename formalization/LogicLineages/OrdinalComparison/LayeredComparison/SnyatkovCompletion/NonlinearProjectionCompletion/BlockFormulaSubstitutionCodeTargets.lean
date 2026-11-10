module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeTargets
open BlockFormulaSubstitutionCode

/-- Literal calibration against the unchanged original atom operation. -/
def LiteralAtomCalibration : Prop := ∀ (i : Nat) (replacement : Term) (a : BlockRows.Atom),
  atom i replacement.encode (atomData a) = atomData (a.substitute i replacement)

/-- One program with name, replacement and the entire atom data as runtime input. -/
def ActualAtomProgram : Prop :=
  Computable (fun p : AtomInput => atom p.1 p.2.1 p.2.2)

def LiteralEncodedAtomCalibration : Prop :=
  ∀ (i : Nat) (replacement : Term) (a : BlockRows.Atom),
    encodedAtom i replacement.encode (Encodable.encode (atomData a)) =
      Encodable.encode (atomData (a.substitute i replacement))

/-- Total all-code payload program, including the fixed malformed fallback. -/
def ActualEncodedAtomProgram : Prop :=
  Computable (fun p : CodeInput => encodedAtom p.1 p.2.1 p.2.2)

/-- Exact code equality for every original block formula, with no shape or
validity premise and no replacement of original substitution semantics. -/
def LiteralFormulaCalibration : Prop :=
  ∀ (i : Nat) (replacement : Term) (p : BlockRows.Formula),
    formula i replacement.encode (formulaCode p) =
      formulaCode (p.substitute i replacement)

/-- One actual program jointly in name, replacement code and numeric formula.
The concrete payload's computability must be proved, not supplied as a premise. -/
def ActualFormulaProgram : Prop :=
  Computable (fun p : CodeInput => formula p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeTargets
