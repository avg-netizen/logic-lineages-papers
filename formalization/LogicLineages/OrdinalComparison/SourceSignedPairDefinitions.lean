module
public import LogicLineages.OrdinalComparison.SourceFunctionalDetectorValuesProof
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions
public import Mathlib.Data.Finsupp.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SignedPair
open OriginalDomain FunctionalDetector

/-- The free abelian Cantor-monomial group. Negative coefficients are integers,
not negative ordinals, and its exponents include all transfinite ordinals. -/
abbrev CantorGroup := Ordinal.{0} →₀ Int

noncomputable def signedCNF (a : Ordinal.{0}) : CantorGroup :=
  (Ordinal.CNF.coeff Ordinal.omega0 a).mapRange
    (fun c => (finiteValue c : Int)) (by simp [finiteValue])

/-- Multiplication by omega moves every exponent e to its successor. This is
natural multiplication, not left ordinal multiplication of the evaluated sum. -/
noncomputable def omegaShift (g : CantorGroup) : CantorGroup :=
  Finsupp.mapDomain (fun e => e + 1) g

inductive Expression (n : Nat) where
  | unit
  | var (i : Fin n)
  | add (a b : Expression n)
  | neg (a : Expression n)
  | shift (a : Expression n)
  deriving Repr

noncomputable def meaning {n} (x : Fin n → Ordinal.{0}) : Expression n → CantorGroup
  | .unit => signedCNF 1
  | .var i => signedCNF (x i)
  | .add a b => meaning x a + meaning x b
  | .neg a => -meaning x a
  | .shift a => omegaShift (meaning x a)

abbrev Context (n : Nat) := List.replicate n unary

def inputVariable : {n : Nat} → Fin n → Variable (Context n) unary
  | _+1, i => Fin.cases .here (fun j => .there (inputVariable j)) i

noncomputable def inputs {n} (ρ : AdmissibleSubstitution (Context n)) (i : Fin n) : Ordinal :=
  closedValue (ρ.vector (inputVariable i) 1)

def identity {Γ} : OriginalTerm Γ unary := .lam (.var .here)
def project {Γ} (a b : OriginalTerm Γ unary) : OriginalTerm Γ unary :=
  .app (.lam (a.rename (Renaming.weaken Γ unary))) b
def liftOmega {Γ} (a : OriginalTerm Γ unary) : OriginalTerm Γ unary :=
  .app (.app (.recC .ground) .zeroC)
    (.lam (a.rename (Renaming.weaken Γ .ground)))

abbrev Pair (Γ : List Ty) := OriginalTerm Γ unary × OriginalTerm Γ unary

def join {Γ} (p q : Pair Γ) : Pair Γ :=
  (combine p.1 q.1, combine p.2 q.2)
def timesEight {Γ} (p : Pair Γ) : Pair Γ :=
  (combine p.1 identity, combine p.2 identity)
def timesSixteen {Γ} (p : Pair Γ) : Pair Γ := join p p

def balanced {Γ} : Nat → (Nat → Pair Γ) → Nat → Pair Γ
  | 0, f, offset => f offset
  | d+1, f, offset => join (balanced d f offset) (balanced d f (offset+2^d))

def constantLeaf {Γ} (i : Nat) : Pair Γ :=
  if i<8 then (combine identity identity, project identity identity)
  else if i<13 then (identity, project identity identity)
  else (identity,identity)
def unitPair {Γ} : Pair Γ := balanced 4 constantLeaf 0

def variablePair {n} (i : Fin n) : Pair (Context n) :=
  join ((timesEight^[3]) (project (.var (inputVariable i)) identity, project identity identity)) unitPair

/-- Adds d+6 to a scale exponent using only factors 8 and 16. -/
def pad {Γ} (d : Nat) (p : Pair Γ) : Pair Γ :=
  (timesSixteen^[d%3]) ((timesEight^[d/3+(2-d%3)]) p)

structure Compiled (n : Nat) where
  pair : Pair (Context n)
  exponent : Nat

def compile {n} : Expression n → Compiled n
  | .unit => ⟨unitPair,12⟩
  | .var i => ⟨variablePair i,15⟩
  | .neg a => let p := compile a; ⟨(p.pair.2,p.pair.1),p.exponent⟩
  | .shift a => let p := compile a
                ⟨(liftOmega p.pair.1,liftOmega p.pair.2),p.exponent+1⟩
  | .add a b =>
      let p := compile a
      let q := compile b
      let k := max p.exponent q.exponent
      ⟨join (pad (k-p.exponent) p.pair) (pad (k-q.exponent) q.pair), k+9⟩

/-- Unrestricted finite integer coefficients and finite omega powers; the one
optional unknown means that products of two unknowns cannot be expressed. -/
structure Monomial (n : Nat) where
  coefficient : Int
  power : Nat
  unknown : Option (Fin n)
  deriving Repr

def zeroExpression {n} : Expression n := .add .unit (.neg .unit)
def repeatExpression {n} (a : Expression n) : Nat → Expression n
  | 0 => zeroExpression
  | k+1 => .add a (repeatExpression a k)
def monomialExpression {n} (m : Monomial n) : Expression n :=
  let base := match m.unknown with | none => Expression.unit | some i => .var i
  let body := repeatExpression ((Expression.shift^[m.power]) base) m.coefficient.natAbs
  if m.coefficient < 0 then .neg body else body

def fromMonomials {n} (ms : List (Monomial n)) : Expression n :=
  ms.foldr (fun m a => .add (monomialExpression m) a) zeroExpression

noncomputable def monomialMeaning {n} (x : Fin n → Ordinal) (m : Monomial n) : CantorGroup :=
  m.coefficient • ((omegaShift^[m.power])
    (signedCNF (match m.unknown with | none => 1 | some i => x i)))
noncomputable def monomialsMeaning {n} (x : Fin n → Ordinal) (ms : List (Monomial n)) : CantorGroup :=
  (ms.map (monomialMeaning x)).sum

noncomputable def difference {Γ} (ρ : AdmissibleSubstitution Γ) (p : Pair Γ) : CantorGroup :=
  signedCNF (FunctionalDetector.Proof.value1 ρ p.1) -
  signedCNF (FunctionalDetector.Proof.value1 ρ p.2)
end LogicLineages.OrdinalComparison.Source.SignedPair
