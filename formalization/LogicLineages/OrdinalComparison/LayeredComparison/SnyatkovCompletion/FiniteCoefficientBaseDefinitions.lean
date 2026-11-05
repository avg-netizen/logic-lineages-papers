module
public import LogicLineages.OrdinalComparison.WWScalarSyntaxCodeDefinitions
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonLayerSyntaxDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBase
open Source Source.ForwardTranslation CommonLayerSyntax

/-- Exact structural finite coefficient evaluator on the ORIGINAL closed positive
syntax. Omega is rejected, never silently made finite. Semantic completeness for
all finite ordinal presentations is not asserted by this definition. -/
def coefficient : ClosedPositive → Option Nat
  | .one => some 1
  | .omega => none
  | .add a b => do return (← coefficient a) + (← coefficient b)
  | .emul a b => do return 2 ^ (← coefficient a) * (← coefficient b)

def iteratePhi : Nat → BaseTerm → BaseTerm
  | 0, t => t
  | k + 1, t => .phi (iteratePhi k t)

def expand (k : Nat) (t : BaseTerm) : BaseTerm :=
  .add (iteratePhi k (.add t (.numeral (2*k)))) (.numeral k)

/-- Literal BASE term compilation of the repository's ORIGINAL source scalar
language, preserving the supplied original variable index map. -/
def compile {ι : Type} (index : ι → Nat) : Scalar ι → Option BaseTerm
  | .one => some (.numeral 1)
  | .var i => some (.variable (index i))
  | .add a b => do return .add (← compile index a) (← compile index b)
  | .shift c a => do return expand (← coefficient c) (← compile index a)

def support {ι : Type} (index : ι → Nat) : Scalar ι → List Nat
  | .one => []
  | .var i => [index i]
  | .add a b => support index a ++ support index b
  | .shift _ a => support index a

def rawIndex {Γ : List Ty} (c : OrdinalComponent Γ) : Nat := SourceTypedPorts.variableIndex c.2.1

namespace Code
def iterate (k code : Nat) : Nat := Nat.rec code (fun _ previous => 4 * previous + 3) k
def expand (k code : Nat) : Nat := 4 * Nat.pair (iterate k (4 * Nat.pair code (4 * (2*k)) + 2)) (4*k) + 2

def coefficient (code : Nat) : Option Nat :=
  if code % 4 = 0 then some 1
  else if code % 4 = 1 then none
  else if code % 4 = 2 then do return (← coefficient (code / 4).unpair.1) + (← coefficient (code / 4).unpair.2)
  else do return 2 ^ (← coefficient (code / 4).unpair.1) * (← coefficient (code / 4).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega

def compile (code : Nat) : Option Nat :=
  if code % 4 = 0 then some code
  else if code % 4 = 1 then some code
  else if code % 4 = 2 then do return 4 * Nat.pair (← compile (code / 4).unpair.1) (← compile (code / 4).unpair.2) + 2
  else do return expand (← coefficient (code / 4).unpair.1) (← compile (code / 4).unpair.2)
termination_by code
decreasing_by
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 4 < code := Nat.div_lt_self hpos (by decide)
    have hl := Nat.unpair_left_le (code / 4)
    have hr := Nat.unpair_right_le (code / 4)
    omega
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteCoefficientBase
