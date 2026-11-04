module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovHyperCollisionDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaDefinitions
public import LogicLineages.OrdinalComparison.ControlResidueDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility
open CommonLayerSyntax CommonHeadCompiler

/-- (source tag, modulus, signed inner offset, signed coefficient, signed
outer constant). Tag0 is Phi(n), tag1 is H(n), all other tags Phi(H(n)+e).
Totalized signed inner offsets retain the actual source domain on the tail. -/
abbrev Parameters := Nat × Nat × Int × Int × Int

def termValue (tag n : Nat) (e : Int) : Nat :=
  if tag = 0 then Phi n else if tag = 1 then FixedSeedControlResidue.H n
  else SnyatkovHyperCollision.translatedValue n e

def cutoff (p : Parameters) : Nat := p.2.1 + p.2.2.1.natAbs + 1

def predicate (p : Parameters) (n : Nat) : Bool :=
  decide ((p.2.2.2.1 * (termValue p.1 n p.2.2.1 : Int) + p.2.2.2.2).natAbs % p.2.1 = 0)

def tailBit (p : Parameters) : Bool :=
  decide ((p.2.2.2.1 * (fastControlResidue p.2.1 : Int) + p.2.2.2.2).natAbs % p.2.1 = 0)

def smallBits (p : Parameters) : List Bool := (List.range (cutoff p)).map (predicate p)

def smallAtom (i : Nat) (p : Parameters) (n : Nat) : BaseFormula.Formula :=
  if predicate p n then .equal (.variable i) (.numeral n) else .falsity

def smallFormula (i : Nat) (p : Parameters) : BaseFormula.Formula :=
  (List.range (cutoff p)).foldr
    (fun n rest => .disjunction (smallAtom i p n) rest) .falsity

/-- Literal pure BASE equality/order formula, with NO divisibility, H, inverse
or source predicate. A tautological equality retains the ONE original variable
exactly, even when every small/tail case is false. -/
def sourceFormula (i : Nat) (p : Parameters) : BaseFormula.Formula :=
  .conjunction (.equal (.variable i) (.variable i))
    (.disjunction (smallFormula i p)
      (.conjunction (.negative (.less (.variable i) (.numeral (cutoff p))))
        (if tailBit p then .truth else .falsity)))

def smallAtomCode (i : Nat) (p : Parameters) (n : Nat) : List Instruction :=
  if predicate p n then [(2, 4 * i + 1, 4 * n)] else [(0, 0, 0)]

def smallCode (i : Nat) (p : Parameters) : List Instruction :=
  (List.range (cutoff p)).foldr
    (fun n rest => smallAtomCode i p n ++ rest ++ [(7, 0, 0)]) [(0, 0, 0)]

/-- Exact postfix ordinary BASE code. Every numerical input is accepted as
coded data; semantic divisibility requires a POSITIVE modulus as in the source. -/
def formulaCode (i : Nat) (p : Parameters) : List Instruction :=
  [(2, 4 * i + 1, 4 * i + 1)] ++ smallCode i p ++
    [(3, 4 * i + 1, 4 * cutoff p), (5, 0, 0)] ++
    (if tailBit p then [(1, 0, 0)] else [(0, 0, 0)]) ++
    [(6, 0, 0), (7, 0, 0), (6, 0, 0)]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovDivisibility
