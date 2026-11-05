module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlock
open NormalForm

/-- Literal summands, including repeated occurrences and zero weights. -/
def occurrences (p : Formula) : List Summand :=
  (LinearRows.atoms p).flatMap (fun a => a.row.2.map Prod.snd)

/-- The original formula is linear at every name in the block. Repetitions
are allowed: the existing named-binder semantics handles shadowing. -/
def allLinear (names : List Nat) (p : Formula) : Bool :=
  names.all (fun i => LinearRows.isLinear i p)

/-- Eliminate innermost binders first, in the original prefix order. -/
def eliminate (names : List Nat) (p : Formula) : Formula :=
  names.foldr LinearRows.eliminate p

namespace Code
/-- The actual numeric test and compiler operate on the existing radix-six
formula code, not on a semantic oracle or an independently chosen valuation. -/
def allLinear (names : List Nat) (code : Nat) : Bool :=
  names.all (fun i => LinearRows.Code.isLinear i code)
def eliminate (names : List Nat) (code : Nat) : Nat :=
  names.foldr LinearRows.Code.eliminate code
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearBlock
