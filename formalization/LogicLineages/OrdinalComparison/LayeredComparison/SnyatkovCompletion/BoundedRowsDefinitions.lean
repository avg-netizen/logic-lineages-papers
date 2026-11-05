module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NormalFormDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRows
open NormalForm

def valueAt (s : Summand) (n : Nat) : Nat := s.term.value (fun _ => n)

/-- Fold precisely the fixed-name occurrences into the integer constant.
All other occurrences, including zero coefficients, retain their order. -/
def splitItems (i n : Nat) (xs : List (Int × Summand)) : Int × List (Int × Summand) :=
  xs.foldr (fun a rest => if a.2.name = i
    then (a.1 * (valueAt a.2 n : Int) + rest.1, rest.2)
    else (rest.1, a :: rest.2)) (0, [])

def rowSubstitute (i n : Nat) (row : Row) : Row :=
  let parts := splitItems i n row.2
  (row.1 + parts.1, parts.2)

/-- Every removed occurrence contributes its original cutoff, regardless of
its coefficient. A false fixed domain must not disappear with the occurrence. -/
def fixedCutoff (i : Nat) (row : Row) : Nat :=
  row.2.foldr (fun a rest => max (if a.2.name = i then a.2.domainCutoff else 0) rest) 0

def atomSubstitute (i n : Nat) : Atom → Atom
  | .nonnegative row => .nonnegative (rowSubstitute i n row)
  | .divisible m row => .divisible m (rowSubstitute i n row)

/-- Substitute through the existing Boolean tree, including any original
domainFormula at its existing position. No global domain guard is inserted. -/
def substitute (i n : Nat) : Formula → Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (atomSubstitute i n a)
  | .negative p => .negative (substitute i n p)
  | .conjunction p q => .conjunction (substitute i n p) (substitute i n q)
  | .disjunction p q => .disjunction (substitute i n p) (substitute i n q)

def any (ps : List Formula) : Formula := ps.foldr Formula.disjunction .falsity
def bounded (i bound : Nat) (p : Formula) : Formula :=
  any ((List.range bound).map (fun n => substitute i n p))
def block (bounds : List (Nat × Nat)) (p : Formula) : Formula :=
  bounds.foldr (fun entry rest => bounded entry.1 entry.2 rest) p

/-- Ordinary named bounded binding, with repeated names and shadowing allowed. -/
def boundedPrefix (ν : Nat → Nat) : List (Nat × Nat) → Formula → Prop
  | [], p => p.eval ν
  | (i, bound) :: rest, p => ∃ n : Nat, n < bound ∧
      boundedPrefix (Function.update ν i n) rest p

/-- Literal strict bound in the existing row language, including bound zero. -/
def boundRow (i bound : Nat) : Row := ((bound : Int) - 1, [(-1, .variable i)])
def boundsFormula (bounds : List (Nat × Nat)) : Formula :=
  bounds.foldr (fun entry rest =>
    .conjunction (.atom (.nonnegative (boundRow entry.1 entry.2))) rest) .truth

namespace Code
abbrev ItemData := NormalForm.Code.ItemData
abbrev RowData := NormalForm.Code.RowData
abbrev AtomData := NormalForm.Code.AtomData

def shift (n : Nat) (e : Int) : Nat := n + e.toNat - (-e).toNat
def itemValue (s : ItemData) (n : Nat) : Nat :=
  if s.1 = 0 then n else if s.1 = 1 then Phi (shift n s.2.2.1)
  else Phi (shift (FixedSeedControlResidue.H (shift n s.2.2.1)) s.2.2.2)
def splitItems (i n : Nat) (xs : List (Int × ItemData)) : Int × List (Int × ItemData) :=
  xs.foldr (fun a rest => if a.2.2.1 = i
    then (a.1 * (itemValue a.2 n : Int) + rest.1, rest.2)
    else (rest.1, a :: rest.2)) (0, [])
def row (i n : Nat) (r : RowData) : RowData :=
  let parts := splitItems i n r.2
  (r.1 + parts.1, parts.2)
def fixedCutoff (i : Nat) (r : RowData) : Nat :=
  r.2.foldr (fun a rest => max (if a.2.2.1 = i
    then NormalForm.Code.itemCutoff a.2 else 0) rest) 0
def atom (i n : Nat) (a : AtomData) : AtomData :=
  (a.1, a.2.1, row i n a.2.2)

/-- Total all-code substitution in the original radix-6 row grammar. -/
def formula (i n code : Nat) : Nat :=
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then
    6 * Encodable.encode (atom i n
      ((Encodable.decode (code / 6) : Option AtomData).getD (0, 0, (0 : Int), []))) + 2
  else if code % 6 = 3 then 6 * formula i n (code / 6) + 3
  else 6 * Nat.pair (formula i n (code / 6).unpair.1)
    (formula i n (code / 6).unpair.2) + code % 6
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 6)
    have hr := Nat.unpair_right_le (code / 6)
    omega

def any (ps : List Nat) : Nat := ps.foldr (fun a b => 6 * Nat.pair a b + 5) 1
def bounded (i bound code : Nat) : Nat :=
  any ((List.range bound).map (fun n => formula i n code))
def block (bounds : List (Nat × Nat)) (code : Nat) : Nat :=
  bounds.foldr (fun entry rest => bounded entry.1 entry.2 rest) code
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRows
