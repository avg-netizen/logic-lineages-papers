module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockSplitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitialization

/-- Literal graph-row class. Every occurrence counts, including repeated,
zero-weight and cancelled entries. This is stronger than plainness. -/
def ZeroShift (p : NormalForm.Formula) : Prop :=
  ∀ a ∈ LinearRows.atoms p, ∀ entry ∈ a.row.2,
    (∃ i : Nat, entry.2 = NormalForm.Summand.variable i) ∨
    (∃ i : Nat, entry.2 = NormalForm.Summand.phi i 0)

/-- Keep exactly the occurrences belonging to the whole bound list. Every
other literal occurrence is moved into BOTH signed parameter terms, even
when its coefficient is zero. Its term uses the original shared valuation. -/
def entries (bound : List Nat) (positive negative : Term) :
    List (Int × NormalForm.Summand) → BlockRows.Row
  | [] => ((positive, negative), [])
  | a :: rest =>
      let r := entries bound positive negative rest
      if bound.contains a.2.name then (r.1, a :: r.2) else
        ((.add (.multiply a.1.toNat a.2.term) r.1.1,
          .add (.multiply (-a.1).toNat a.2.term) r.1.2), r.2)

def row (bound : List Nat) (r : NormalForm.Row) : BlockRows.Row :=
  entries bound (.numeral r.1.toNat) (.numeral (-r.1).toNat) r.2

def atom (bound : List Nat) : NormalForm.Atom → BlockRows.Atom
  | .nonnegative r => .nonnegative (row bound r)
  | .divisible m r => .divisible m (row bound r)

def «initialize» (bound : List Nat) : NormalForm.Formula → BlockRows.Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => .atom (atom bound a)
  | .negative p => .negative («initialize» bound p)
  | .conjunction p q => .conjunction («initialize» bound p) («initialize» bound q)
  | .disjunction p q => .disjunction («initialize» bound p) («initialize» bound q)

/-- The existing concrete projector and its actual bound-length runner are
unchanged. This wrapper does not assume or assert numeric effectivity. -/
def project (bound : List Nat) (p : NormalForm.Formula) : Matrix :=
  PlainBlockSplit.project bound («initialize» bound p)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.WholeBoundInitialization
