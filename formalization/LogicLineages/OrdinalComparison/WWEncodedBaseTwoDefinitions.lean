module
public import LogicLineages.OrdinalComparison.RawNotationCodeDefinitions
public import LogicLineages.OrdinalComparison.WWClosedPositiveEvaluationDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Literal raw-note subtraction of one on the left. Infinite leading
exponents are unchanged; this is not a right-predecessor operation. -/
def rawSubtractOneCode (n : Nat) : Nat :=
  if n = 0 then 0 else
    let p := n.pred.unpair
    if p.1 = 0 then
      if p.2.unpair.1 = 0 then p.2.unpair.2
      else Nat.pair 0 (Nat.pair (p.2.unpair.1 - 1) p.2.unpair.2) + 1
    else n

/-- Numerical ONote.split': the quotient by omega and finite remainder.
This differs from the accepted rawSplitCode's unchanged limit-part output. -/
def rawSplitPrimeCode : Nat → Nat
  | 0 => 0
  | n+1 =>
    let e := n.unpair.1
    let c := n.unpair.2.unpair.1
    let t := n.unpair.2.unpair.2
    if e = 0 then Nat.pair 0 (c+1) else
      let p := (rawSplitPrimeCode t).unpair
      Nat.pair (Nat.pair (rawSubtractOneCode e) (Nat.pair c p.1) + 1) p.2
termination_by n => n
decreasing_by exact Nat.lt_succ_of_le ((Nat.unpair_right_le _).trans (Nat.unpair_right_le n))

/-- Exact base-two ordinal exponentiation: after a=omega*b+k, return the
normal monomial omega^b * 2^k. All arithmetic on codes is numerical. -/
def encodedBaseTwoPower (n : Nat) : Nat :=
  let p := (rawSplitPrimeCode n).unpair
  Nat.pair p.1 (Nat.pair (2 ^ p.2 - 1) 0) + 1
end LogicLineages.OrdinalComparison
