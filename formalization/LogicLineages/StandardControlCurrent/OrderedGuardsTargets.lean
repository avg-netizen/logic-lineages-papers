module
public import LogicLineages.StandardControlCurrent.OrderedGuardsDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedGuardsTargets
open OrdinalComparison PolynomialGraphCompletion FullWordGuardCompletion
open CanonicalGuardSelector GuardChildMeasureCompletion

def WordCalibration : Prop := ∀ D w, WordAllowed D w → ∀ t,
  (OrderedGuards.WordDomain w t ↔ PolynomialGraphCompletion.WordDomain w t) ∧
  (OrderedGuards.WordDomain w t → OrderedGuards.wordValue w t = PolynomialGraphCompletion.wordValue w t)

def CompilerCalibration : Prop := ∀ D p,
  (admitted D p = false → compile D p = invalidPackage) ∧
  (admitted D p = true →
    compile D p = finish p (leastFuel D p) ∧
    selectWords (run p (leastFuel D p)).1.1 (run p (leastFuel D p)).1.2 = none ∧
    ∀ n, n < leastFuel D p →
      selectWords (run p n).1.1 (run p n).1.2 ≠ none)

def CompiledSyntax : Prop := ∀ D p, 3 ≤ D → admitted D p = true →
  RowAllowed D (packageRow (compile D p)) ∧
  LinearInMaximum (packageRow (compile D p)) ∧
  (∀ desired sign, desired ≤ 2 →
    sign ∈ guardAt (packageGuards (compile D p)) desired → sign ≤ 2) ∧
  packageSame (compile D p) ≤ 2 ∧
  p ∈ packageTrace (compile D p) ∧
  ∀ q ∈ packageTrace (compile D p), admitted D q = true

/-- The common computed cutoff pays all actual successive domains, for
the original words, every selected child, their canonical prepared forms,
and the emitted word-linear row. -/
def CompiledDomains : Prop := ∀ D p, 3 ≤ D → admitted D p = true →
  ∀ x y, packageTail (compile D p) ≤ x → packageTail (compile D p) ≤ y →
  OrderedGuards.WordDomain p.1 x ∧ OrderedGuards.WordDomain p.2 y ∧
  RowDomain (packageRow (compile D p)) (pairEnv x y) ∧
  ∀ q ∈ packageTrace (compile D p),
    OrderedGuards.WordDomain q.1 x ∧ OrderedGuards.WordDomain q.2 y ∧
    OrderedGuards.WordDomain (preparedWord q.1) x ∧ OrderedGuards.WordDomain (preparedWord q.2) y

/-- Exact finite Boolean guards for all three comparisons under the
source's maximum-variable order; names zero and one are never refreshed. -/
def CompiledThreeWay : Prop := ∀ D p, 3 ≤ D → admitted D p = true →
  ∀ x y, packageTail (compile D p) ≤ x → packageTail (compile D p) ≤ y → y ≤ x →
    (OrderedGuards.wordValue p.1 x < OrderedGuards.wordValue p.2 y ↔
      GuardHolds (guardAt (packageGuards (compile D p)) 0)
        (packageRow (compile D p)) (pairEnv x y)) ∧
    (OrderedGuards.wordValue p.1 x = OrderedGuards.wordValue p.2 y ↔
      GuardHolds (guardAt (packageGuards (compile D p)) 1)
        (packageRow (compile D p)) (pairEnv x y)) ∧
    (OrderedGuards.wordValue p.2 y < OrderedGuards.wordValue p.1 x ↔
      GuardHolds (guardAt (packageGuards (compile D p)) 2)
        (packageRow (compile D p)) (pairEnv x y))

/-- The same-variable answer is a fixed computed value, independent of
the eventual raw input; it is not a residual self-dependent word guard. -/
def CompiledSameVariable : Prop := ∀ D p, 3 ≤ D → admitted D p = true →
  ∀ x, packageTail (compile D p) ≤ x →
    orderNat (OrderedGuards.wordValue p.1 x) (OrderedGuards.wordValue p.2 x) = packageSame (compile D p)

def BoundedCompilerPrograms : Prop :=
  Primrec (fun p : Nat × Nat => signFormula p.1 p.2) ∧ Primrec makeGuards ∧
  Primrec (fun p : Guards × Nat => guardAt p.1 p.2) ∧
  Primrec terminalRow ∧ Primrec terminalTail ∧ Primrec terminalSame ∧
  Primrec (fun p : WordPair × Nat => finiteTrace p.1 p.2) ∧
  Primrec (fun p : WordPair × Nat => finish p.1 p.2)

def CompilerProgram : Prop := Computable (fun p : Nat × WordPair => compile p.1 p.2)


def Full : Prop := WordCalibration ∧ CompilerCalibration ∧ CompiledSyntax ∧ CompiledDomains ∧
  CompiledThreeWay ∧ CompiledSameVariable ∧ BoundedCompilerPrograms ∧ CompilerProgram
end LogicLineages.StandardControlCurrent.OrderedGuardsTargets
