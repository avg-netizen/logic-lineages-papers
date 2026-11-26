module
public import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearTargets

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedStripReconstruction
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection FiniteStripRecovery FiniteStripCollectorRecovery

abbrev StripCodeArgs := Nat × Nat × List NamedCode × Nat

/-- Literal old radix-six formula fold after actual correlated reads.
Invalid and genuine miss remain different statuses; neither becomes false. -/
noncomputable def specializeCode (f : Nat → Nat) (q : StripCodeArgs) : Option (Option Nat) :=
  (collectCode f q.1 q.2.1 q.2.2.1).map (fun r => r.map (fun reads => foldCode reads q.2.2.2))

/-- This checker rejects a nonconstant residual matrix. It never evaluates
nonlinear summands using an invented zero assignment. -/
def constantCheck (code : Nat) : Option Bool :=
  if ClosedLinear.Code.constantMatrix code then some (ClosedLinear.Code.evaluateConstants code) else none

/-- The three option levels distinguish invalid read, genuine miss,
nonconstant residual, and a genuine checked Boolean answer. -/
noncomputable def checkStripCode (f : Nat → Nat) (q : StripCodeArgs) : Option (Option (Option Bool)) :=
  (specializeCode f q).map (fun r => r.map constantCheck)

def PreparedInput (rs : List NamedOperand) (p : NormalForm.Formula) : Prop :=
  PlainPreparedFormula p ∧ (∀ r ∈ rs, 0 < r.1) ∧ (rs.map Prod.fst).Nodup ∧
    ∀ i ∈ p.variables, i ∈ rs.map Prod.fst

def CodeExact : Prop :=
  (∀ f : Nat → Nat, Computable f → Computable (specializeCode f) ∧ Computable (checkStripCode f)) ∧
  (∀ (f : Nat → Nat) (x a : Nat) (rs : List NamedCode) (code : Nat),
    (collectCode f x a rs = none → specializeCode f (x,a,rs,code) = none) ∧
    (collectCode f x a rs = some none → specializeCode f (x,a,rs,code) = some none)) ∧
  ∀ (f : Nat → Nat) (x a : Nat) (rs : List NamedCode) (reads : List (Nat × Nat))
      (p : NormalForm.Formula),
    collectCode f x a rs = some (some reads) →
    specializeCode f (x,a,rs,p.encode) = some (some (foldFormula reads p).encode)

/-- No pre-supplied fixed outputs or fully tied mu. The actual successful
reads must construct them. Only genuinely untouched named fields are supplied
at the one common raw rho; its other coordinates remain unbounded. -/
def HitReconstruction : Prop :=
  ∀ (f : Nat → Nat) (x a : Nat) (rs : List NamedOperand) (p : NormalForm.Formula)
      (reads : List (Nat × Nat)) (ρ ν : Nat → Nat),
    PreparedInput rs p → collectCode f x a (rs.map encodeRequest) = some (some reads) →
    ρ x = a →
    (∀ r ∈ rs, r.2.rank ≠ x → LowerOperandActual f ρ r.2 (ν r.1)) →
    let μ := foldValuation reads ν
    (∀ r ∈ rs, LowerOperandActual f ρ r.2 (μ r.1)) ∧
    ((foldFormula reads p).eval ν ↔ p.eval μ) ∧
    PlainPreparedFormula (foldFormula reads p) ∧
    ∀ i ∈ (foldFormula reads p).variables,
      ∃ r ∈ rs, r.1 = i ∧ r.2.rank ≠ x

/-- Genuine zero-remaining-live-rank terminal case at the original row.
An answer is produced by the actual closed checker, not supplied as an oracle.
This does not claim an entire infinite strip has no surviving rank. -/
def ClosedHitDecision : Prop :=
  ∀ (f : Nat → Nat) (x a : Nat) (rs : List NamedOperand) (p : NormalForm.Formula)
      (reads : List (Nat × Nat)),
    PreparedInput rs p → (∀ r ∈ rs, r.2.rank = x) →
    collectCode f x a (rs.map encodeRequest) = some (some reads) →
    let μ := foldValuation reads (fun _ => 0)
    ∃ answer : Bool,
      checkStripCode f (x,a,rs.map encodeRequest,p.encode) = some (some (some answer)) ∧
      (p.eval μ ↔ answer = true) ∧
      ∀ ρ : Nat → Nat, ρ x = a → ∀ r ∈ rs, LowerOperandActual f ρ r.2 (μ r.1)

/-- Prepared same-rank actual glue only. Field/residue-to-row preparation,
required-call guards, table/name-zero routing, low-strip coverage and full
printed arithmetic remain separate unpaid obligations. -/
def FullPreparedStripReconstruction : Prop := CodeExact ∧ HitReconstruction ∧ ClosedHitDecision
end LogicLineages.PermittedControl.PreparedStripReconstruction
