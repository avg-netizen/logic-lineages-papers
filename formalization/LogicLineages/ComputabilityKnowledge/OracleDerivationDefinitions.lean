module

public import LogicLineages.ComputabilityKnowledge.OracleProgramDefinitions

@[expose] public section
/-! Finite computation derivations for a total oracle. Prior μ computations
are all present, not only the first witnessed zero. This stage makes no
claim that the relation has yet been turned into a relative verifier. -/
namespace LogicLineages.ComputabilityKnowledge.OracleDerivation
open OracleProgram

inductive Derives (g : Nat → Nat) : Program → Nat → Nat → Prop where
  | base (c : Nat.Partrec.Code) (input output fuel : Nat)
      (halts : Nat.Partrec.Code.evaln fuel c input = some output) :
      Derives g (.base c) input output
  | query (input : Nat) : Derives g .query input (g input)
  | pair {p q : Program} {input left right : Nat}
      (hp : Derives g p input left) (hq : Derives g q input right) :
      Derives g (.pair p q) input (Nat.pair left right)
  | comp {p q : Program} {input intermediate output : Nat}
      (hq : Derives g q input intermediate) (hp : Derives g p intermediate output) :
      Derives g (.comp p q) input output
  | precZero {p q : Program} {parameter output : Nat}
      (hp : Derives g p parameter output) :
      Derives g (.prec p q) (Nat.pair parameter 0) output
  | precSucc {p q : Program} {parameter index previous output : Nat}
      (hprev : Derives g (.prec p q) (Nat.pair parameter index) previous)
      (hstep : Derives g q (Nat.pair parameter (Nat.pair index previous)) output) :
      Derives g (.prec p q) (Nat.pair parameter (index + 1)) output
  | mu {p : Program} {parameter : Nat} (prior : List Nat)
      (runs : ∀ j : Nat, j < prior.length → Derives g p (Nat.pair parameter j) (prior.getD j 0))
      (nonzero : ∀ j : Nat, j < prior.length → prior.getD j 0 ≠ 0)
      (last : Derives g p (Nat.pair parameter prior.length) 0) :
      Derives g (.mu p) parameter prior.length

end LogicLineages.ComputabilityKnowledge.OracleDerivation
