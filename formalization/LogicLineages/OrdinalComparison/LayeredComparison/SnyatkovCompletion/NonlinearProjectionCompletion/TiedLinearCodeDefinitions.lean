module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCode

/-- Roles remain distinct even when parameter and occurrence values agree.
Tag zero carries an original term code; tag one carries encoded item data. -/
abbrev TokenData := Nat × Nat

def tokenData : TiedLinear.Token → TokenData
  | .parameter t => (0, t.encode)
  | .occurrence s => (1, Encodable.encode s.data)

def variableItem (j : Nat) : NormalForm.Code.ItemData := (0, j, 0, 0)
def rawToken (x : Nat) : TokenData := (1, Encodable.encode (variableItem x))

def rowTokens (r : BlockRowSubstitutionCode.RowData) : List TokenData :=
  [(0, r.1.1), (0, r.1.2)] ++ r.2.map (fun a => (1, Encodable.encode a.2))

def tokens (code : Nat) : List TokenData :=
  (LinearRows.Code.atoms code).flatMap (fun payload =>
    rowTokens (BlockFormulaSubstitutionCode.decodeAtom payload).2.2)

/-- The distinguished original raw variable has name zero; every other token
uses the first literal table occurrence plus one. Repeated tokens are retained. -/
def tokenName (table : List TokenData) (x : Nat) (t : TokenData) : Nat :=
  if t = rawToken x then 0 else table.idxOf t + 1

def tokenOfName (table : List TokenData) (x j : Nat) : TokenData :=
  if j = 0 then rawToken x else table[j - 1]?.getD (0, WindowCode.numeral 0)

def liftRow (table : List TokenData) (x : Nat)
    (r : BlockRowSubstitutionCode.RowData) : NormalForm.Code.RowData :=
  (0, (1, variableItem (tokenName table x (0, r.1.1))) ::
    (-1, variableItem (tokenName table x (0, r.1.2))) ::
    r.2.map (fun a => (a.1, variableItem (tokenName table x (1, Encodable.encode a.2)))))

def liftAtom (table : List TokenData) (x : Nat)
    (a : BlockFormulaSubstitutionCode.AtomData) : NormalForm.Code.AtomData :=
  (a.1, a.2.1, liftRow table x a.2.2)

def liftEncodedAtom (table : List TokenData) (x code : Nat) : Nat :=
  Encodable.encode (liftAtom table x (BlockFormulaSubstitutionCode.decodeAtom code))

def liftFormula (table : List TokenData) (x code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (liftEncodedAtom table x) code

/-- Explicit total extension for malformed occurrence payloads. -/
def decodeItem (code : Nat) : NormalForm.Code.ItemData :=
  (Encodable.decode code).getD (variableItem 0)

/-- Exactly the original lowering fallback for every non-variable summand. -/
def lowerSummand (table : List TokenData) (x : Nat)
    (s : NormalForm.Code.ItemData) : TokenData :=
  if s.1 = 0 then tokenOfName table x s.2.1 else (0, WindowCode.numeral 0)

/-- Tail-first lowering preserves the source token's role. Only parameter
codes enter the signed constants; occurrence tokens remain actual occurrences. -/
def lowerStep (table : List TokenData) (x : Nat) (a : BlockRowSubstitutionCode.EntryData)
    (r : BlockRowSubstitutionCode.RowData) : BlockRowSubstitutionCode.RowData :=
  let t := lowerSummand table x a.2
  if t.1 = 0 then
    ((WindowCode.add (WindowCode.multiply a.1.toNat t.2) r.1.1,
      WindowCode.add (WindowCode.multiply (-a.1).toNat t.2) r.1.2), r.2)
  else (r.1, (a.1, decodeItem t.2) :: r.2)

def lowerEntries (table : List TokenData) (x positive negative : Nat)
    (es : List BlockRowSubstitutionCode.EntryData) : BlockRowSubstitutionCode.RowData :=
  es.foldr (lowerStep table x) ((positive, negative), [])

def lowerRow (table : List TokenData) (x : Nat)
    (r : NormalForm.Code.RowData) : BlockRowSubstitutionCode.RowData :=
  lowerEntries table x (WindowCode.numeral r.1.toNat) (WindowCode.numeral (-r.1).toNat) r.2

def lowerAtom (table : List TokenData) (x : Nat)
    (a : NormalForm.Code.AtomData) : BlockFormulaSubstitutionCode.AtomData :=
  (a.1, a.2.1, lowerRow table x a.2.2)

def lowerEncodedAtom (table : List TokenData) (x code : Nat) : Nat :=
  Encodable.encode (lowerAtom table x (LinearRows.Code.decodeAtom code))

def lowerFormula (table : List TokenData) (x code : Nat) : Nat :=
  LinearRows.Code.mapAtoms (lowerEncodedAtom table x) code

/-- The SAME original table/lift/Cooper/lower algorithm. The existing actual
numeric Cooper kernel eliminates name zero; no solver is supplied as input. -/
def eliminate (x code : Nat) : Nat :=
  let table := tokens code
  lowerFormula table x (LinearRows.Code.eliminate 0 (liftFormula table x code))

abbrev AdapterInput := List TokenData × (Nat × Nat)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCode
