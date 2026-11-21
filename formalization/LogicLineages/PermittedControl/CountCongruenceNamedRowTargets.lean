module
public import LogicLineages.PermittedControl.ShortFieldPreprocessingTargets
public import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryTargets
public import LogicLineages.PermittedControl.EntryTargets

@[expose] public section
namespace LogicLineages.PermittedControl.CountCongruenceNamedRow
open OrdinalComparison FieldComparison PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

/-- One original count together with a raw identity contribution at the
same original rank. The coefficients and constant are unrestricted integers. -/
abbrev RawArgs := Nat × Nat × Nat × Nat × Int × Int × Int

def rawArgs (m rank : Nat) (lam mu : NONote) (c u v : Int) : RawArgs :=
  (m,rank,rawNoteEncode lam.1,rawNoteEncode mu.1,c,u,v)

def requests (rank : Nat) : List NamedOperand := [(1,.coordinate rank)]

def residueCount (k nmu j : Nat) : Int :=
  if k = 0 then ((j / 2 : Nat) : Int) - (((nmu + 1) / 2 : Nat) : Int) else (k : Int)

/-- The absolute-value encoding is only a decidable divisibility test.
It does not turn any summand of the original signed row into a natural. -/
def keepResidue (m k nmu j : Nat) (c u v : Int) : Bool :=
  decide ((c + u * (j : Int) + v * residueCount k nmu j).natAbs % m = 0)

def residueAtom (m j : Nat) : NormalForm.Formula :=
  .atom (.divisible (2*m-1) (-(j : Int),[(1,.variable 1)]))

def row (m k nmu : Nat) (c u v : Int) : NormalForm.Formula :=
  (List.range (2*m)).foldr
    (fun j tail => if keepResidue m k nmu j c u v then
      .disjunction (residueAtom m j) tail else tail) .falsity

/-- Literal radix-six code of the actual divisibility atom, not a fresh
formula representation. Its unique variable is fixed positive name 1. -/
def residueAtomCode (m j : Nat) : Nat :=
  let data : NormalForm.Code.AtomData := (1,2*m-1,(-(j : Int),[(1,(0,1,0,0))]))
  6 * Encodable.encode data + 2

def rowCode (m k nmu : Nat) (c u v : Int) : Nat :=
  (List.range (2*m)).foldr
    (fun j tail => if keepResidue m k nmu j c u v then
      6 * Nat.pair (residueAtomCode m j) tail + 5 else tail) 1

/-- Numeric program, uniform on raw codes. Modulus zero is rejected. On
other malformed endpoint codes no mathematical interpretation is claimed. -/
def prepareCode (q : RawArgs) : Option (List NamedCode × Nat) :=
  let (m,rank,lam,mu,c,u,v) := q
  if m = 0 then none else
    some ([(1,(0,rank,(0,0,0,0)))],
      rowCode m (shortGapLengthCode lam mu) (rawNormCode mu) c u v)

def tailCode (B lam mu m : Nat) : Nat :=
  max (rawNormCode lam) (max (rawNormCode mu + 3) (max m B))

def CodeExact : Prop :=
  Primrec prepareCode ∧
  Primrec (fun z : Nat × Nat × Nat × Nat => tailCode z.1 z.2.1 z.2.2.1 z.2.2.2) ∧
  (∀ q : RawArgs, q.1 = 0 → prepareCode q = none) ∧
  (∀ (B m : Nat) (lam mu : NONote),
    tailCode B (rawNoteEncode lam.1) (rawNoteEncode mu.1) m =
      max (actualOrdinalNorm lam.1.repr) (max (actualOrdinalNorm mu.1.repr + 3) (max m B))) ∧
  ∀ (m rank : Nat) (lam mu : NONote) (c u v : Int), 0 < m →
    prepareCode (rawArgs m rank lam mu c u v) =
      some ((requests rank).map encodeRequest,
        (row m (shortGapLength lam mu) (actualOrdinalNorm mu.1.repr) c u v).encode)

def ShapeAndSupport : Prop :=
  (∀ (lam mu : NONote), ProperField (.entry 0 lam mu) →
    (shortGapLength lam mu = 0 ↔ LongField (.entry 0 lam mu)) ∧
    ∀ k : Nat, 0 < k → (shortGapLength lam mu = k ↔
      lam.1.repr = mu.1.repr + Ordinal.omega0 * (k : Ordinal))) ∧
  ∀ (m rank k nmu : Nat) (c u v : Int),
    let rs := requests rank
    let p := row m k nmu c u v
    PlainPreparedFormula p ∧ (∀ r ∈ rs, 0 < r.1) ∧ (rs.map Prod.fst).Nodup ∧
    ∀ i ∈ p.variables, i ∈ rs.map Prod.fst

/-- The actual original entry success and its true domain are conclusions.
Only the source tail is required. The row tests one shared raw residue
of the same x for the signed identity and signed count contributions. -/
def ActualNamedRow : Prop :=
  ∀ (f : Nat → Nat) (B : Nat), SelectedWithThreshold f B →
  ∀ (m rank : Nat) (lam mu : NONote) (c u v : Int) (ρ : Nat → Nat),
    0 < m → ProperField (.entry 0 lam mu) →
    let x := ρ rank
    tailCode B (rawNoteEncode lam.1) (rawNoteEncode mu.1) m ≤ x →
    let p := row m (shortGapLength lam mu) (actualOrdinalNorm mu.1.repr) c u v
    ∃ i : Nat,
      FirstEntry f (countInitial lam.1.repr x) mu.1.repr i ∧
      ClosedOrdinaryValueDomain (.entry 0 lam mu) x ∧
      LowerOperandActual f ρ (.count rank lam mu) i ∧
      lowerOperandRead f ρ (.count rank lam mu) = some (some i) ∧
      (∀ ν : Nat → Nat, ν 1 = x →
        p.eval ν ↔ (m : Int) ∣ c + u * (x : Int) + v * (i : Int))

/-- One count-congruence adapter, not all mixed modular rows or whole #704. -/
def FullCountCongruenceNamedRow : Prop := CodeExact ∧ ShapeAndSupport ∧ ActualNamedRow

end LogicLineages.PermittedControl.CountCongruenceNamedRow
