module
public import LogicLineages.OrdinalComparison.WWScalarTranslationDefinitions
public import LogicLineages.OrdinalComparison.EncodedPositiveFoldDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

/-- Actual normal notation for the compiler's fixed omega-natural-product head. -/
def scalarHeadNote (c : ClosedPositive) : NONote :=
  naturalProduct ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩ c.evaluate

/-- Numeric scalar syntax with shared input indices, compatible with the
accepted positive-expression code after positive tuple substitution. -/
def scalarCode {ι : Type} (index : ι → Nat) : Scalar ι → Nat
  | .one => 4
  | .var x => 4 * index x + 1
  | .add a b => 4 * Nat.pair (scalarCode index a) (scalarCode index b) + 2
  | .shift c a => 4 * Nat.pair (rawNoteEncode (scalarHeadNote c).1) (scalarCode index a) + 3

/-- Zero-based tuple entries denote positive source inputs by successor;
repeated variables use the exact same tuple coordinate. -/
def scalarGround {ι : Type} (index : ι → Nat) (xs : List Nat) : Scalar ι → FixedLimitPositiveExpr
  | .one => .constant 1
  | .var x => .constant (xs.getD (index x) 0 + 1)
  | .add a b => .add (scalarGround index xs a) (scalarGround index xs b)
  | .shift c a => .head (scalarHeadNote c) (scalarGround index xs a)

/-- Total numerical substitution, including explicit behavior on every raw
code. This does not assume parser success or any semantic oracle. -/
def instantiateScalarCode (xs : List Nat) (n : Nat) : Nat :=
  if h0 : n % 4 = 0 then n
  else if h1 : n % 4 = 1 then 4 * (xs.getD (n / 4) 0 + 1)
  else
    have hn : 0 < n := by omega
    have hd : n / 4 < n := Nat.div_lt_self hn (by decide)
    let p := (n / 4).unpair
    have hl : p.1 < n := (Nat.unpair_left_le _).trans_lt hd
    have hr : p.2 < n := (Nat.unpair_right_le _).trans_lt hd
    if n % 4 = 2 then
      4 * Nat.pair (instantiateScalarCode xs p.1) (instantiateScalarCode xs p.2) + 2
    else 4 * Nat.pair p.1 (instantiateScalarCode xs p.2) + 3
termination_by n
decreasing_by all_goals assumption

/-- The accepted actual collapse program executes the fully grounded code.
Its genuine uniform Computable certificate is a separate obligation. -/
noncomputable def encodedScalarValue (n : Nat) (xs : List Nat) : Nat :=
  encodedPositiveFoldValue (instantiateScalarCode xs n)
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
