module
public import LogicLineages.PermittedControl.FiniteStripRecoveryTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FiniteStripCollectorRecovery
open OrdinalComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection FieldComparison

abbrev NamedCode := Nat × LowerOperandCode
abbrev NamedOperand := Nat × LowerOperand
abbrev ReadResult := Option (Option (List (Nat × Nat)))

/-- Validate ORIGINAL raw tags and unused payload before using the closed
field reader. Nonzero arbitrary field tags must not masquerade as entries. -/
def operandShape (c : LowerOperandCode) : Bool :=
  if c.1 = 0 then decide (c.2.2 = (0,0,0,0))
  else if c.1 = 1 then decide
    ((c.2.2.1 = 0 ∧ c.2.2.2.2.1 = 0 ∧ c.2.2.2.2.2 = 0) ∨ c.2.2.1 = 1)
  else decide (c.1 = 2 ∧ c.2.2.1 = 1 ∧ c.2.2.2.1 = 0)

noncomputable def fieldRead (f : Nat → Nat) (a : Nat) (c : LowerOperandCode) :
    ClosedNaturalFieldResult :=
  if c.1 = 0 then some (some a)
  else if c.1 = 1 then closedOrdinaryValueField f c.2.2 a
  else closedOrdinaryCountField f (c.2.2.2.2.1,c.2.2.2.2.2,a)

/-- Name zero is rejected. It has NO implicit fixed-rank alias in this packet.
Every matched original operand is read at the SAME actual unshifted a. -/
noncomputable def readCode (f : Nat → Nat) (x a : Nat) (r : NamedCode) : ReadResult :=
  if r.1 = 0 ∨ operandShape r.2 = false then none
  else if r.2.2.1 ≠ x then some (some [])
  else (fieldRead f a r.2).map (fun v => v.map (fun b => [(r.1,b)]))

/-- Preserve the first read failure. A later invalid read does not replace an
earlier genuine miss. No failure is converted into formula falsity. -/
def appendResult (head tail : ReadResult) : ReadResult :=
  match head with
  | none => none
  | some none => some none
  | some (some hs) => tail.map (fun ts => ts.map (hs ++ ·))

noncomputable def collectCode (f : Nat → Nat) (x a : Nat) (rs : List NamedCode) : ReadResult :=
  rs.foldr (fun r tail => appendResult (readCode f x a r) tail) (some (some []))

noncomputable def expectedRead (f : Nat → Nat) (x a : Nat) (r : NamedOperand) : ReadResult :=
  if r.1 = 0 then none
  else if r.2.rank ≠ x then some (some [])
  else (lowerOperandRead f (fun _ => a) r.2).map (fun v => v.map (fun b => [(r.1,b)]))

noncomputable def expectedCollect (f : Nat → Nat) (x a : Nat)
    (rs : List NamedOperand) : ReadResult :=
  rs.foldr (fun r tail => appendResult (expectedRead f x a r) tail) (some (some []))

def encodeRequest (r : NamedOperand) : NamedCode := (r.1,r.2.code)

def CollectorEffective : Prop :=
  ∀ f : Nat → Nat, Computable f →
    Computable₂ (fun p : Nat × Nat => readCode f p.1 p.2) ∧
    Computable₂ (fun p : Nat × Nat => collectCode f p.1 p.2)

/-- Literal canonical operand calibration includes invalid/genuine-miss/hit
statuses, not just successful numeral values. All raw malformed tags are
handled by operandShape rather than the permissive old field dispatch. -/
def CollectorReadExact : Prop :=
  (∀ op : LowerOperand, operandShape op.code = true) ∧
  (∀ (f : Nat → Nat) (x a : Nat) (r : NamedOperand),
    readCode f x a (encodeRequest r) = expectedRead f x a r) ∧
  ∀ (f : Nat → Nat) (x a : Nat) (rs : List NamedOperand),
    collectCode f x a (rs.map encodeRequest) = expectedCollect f x a rs

/-- Successful reads only. The single rho controls ALL original ranks and
nonlinear calls; mu is tied to that one actual assignment. Other raw ranks
remain unbounded. Positive distinct names are the actual named slots; no
reserved-zero premise is silently added. -/
def CollectorHitFold : Prop :=
  ∀ (f : Nat → Nat) (x a : Nat) (rs : List NamedOperand)
      (reads : List (Nat × Nat)) (p : NormalForm.Formula)
      (ρ ν μ : Nat → Nat),
    (∀ r ∈ rs, 0 < r.1) → (rs.map Prod.fst).Nodup →
    (∀ i ∈ p.variables, i ∈ rs.map Prod.fst) →
    collectCode f x a (rs.map encodeRequest) = some (some reads) →
    ρ x = a →
    (∀ r ∈ rs, LowerOperandActual f ρ r.2 (μ r.1)) →
    (∀ r ∈ rs, r.2.rank ≠ x → ν r.1 = μ r.1) →
    ((FiniteStripRecovery.foldFormula reads p).eval ν ↔ p.eval μ)

/-- Narrow same-rank read collector, not table lookup/preparation, name-zero
aliasing, failure-implies-empty-domain, strip coverage, or arithmetic QE. -/
def FullCollector : Prop := CollectorEffective ∧ CollectorReadExact ∧ CollectorHitFold
end LogicLineages.PermittedControl.FiniteStripCollectorRecovery
