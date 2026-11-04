module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.OmegaSeedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler
open OriginalDomain SignedPair

/-- The last expression index denotes the one closed Omega seed. The source
context still has exactly the n original unknowns; no new free seed is added. -/
noncomputable def seededInputs {n : Nat}
    (ρ : AdmissibleSubstitution (Context n)) (i : Fin (n+1)) : Ordinal :=
  if h : i.val<n then inputs ρ ⟨i.val,h⟩ else OmegaSeed.omega

noncomputable def linearMeaning {n : Nat} (x : Fin n → CantorGroup) :
    Expression n → CantorGroup
  | .unit => signedCNF 1
  | .var i => x i
  | .add a b => linearMeaning x a+linearMeaning x b
  | .neg a => -linearMeaning x a
  | .shift a => omegaShift (linearMeaning x a)

/-- Substitute x_i-Omega for every occurrence of an original unknown. The
entire system shares the same original indices and the same literal seed. -/
def subtractSeed {n : Nat} : Expression n → Expression (n+1)
  | .unit => .unit
  | .var i => .add (.var i.castSucc) (.neg (.var (Fin.last n)))
  | .add a b => .add (subtractSeed a) (subtractSeed b)
  | .neg a => .neg (subtractSeed a)
  | .shift a => .shift (subtractSeed a)

/-- The original compiler with one additional CLOSED branch. Every arithmetic
operation and scale alignment is the already checked signed-pair construction. -/
def compile {n : Nat} : Expression (n+1) → Compiled n
  | .unit => ⟨unitPair,12⟩
  | .var i => if h : i.val<n then ⟨variablePair ⟨i.val,h⟩,15⟩
      else ⟨OmegaSeed.pair,12⟩
  | .neg a => let p := compile a; ⟨(p.pair.2,p.pair.1),p.exponent⟩
  | .shift a => let p := compile a
                ⟨(liftOmega p.pair.1,liftOmega p.pair.2),p.exponent+1⟩
  | .add a b =>
      let p := compile a
      let q := compile b
      let k := max p.exponent q.exponent
      ⟨join (pad (k-p.exponent) p.pair) (pad (k-q.exponent) q.pair),k+9⟩

/-- No zero-pattern disjunction occurs at this endpoint. Zero polynomial
unknowns are represented by the positive ordinal Omega itself. -/
def OrdinalSatisfiable {n : Nat} (s : System n) : Prop :=
  ∃ ρ : AdmissibleSubstitution (Context n),
    ∀ d ∈ s, meaning (seededInputs ρ) (subtractSeed d)=0

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.SeededCompiler
