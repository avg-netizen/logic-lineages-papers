module
public import LogicLineages.PermittedControl.ThickBlockTargets

@[expose] public section
namespace LogicLineages.PermittedControl.Targets
open OrdinalComparison

/-- Fixed original-unit retained prefix. Its norm bound is not a claim about
arbitrary dynamically generated prefixes. All states and clocks are actual. -/
def SensitiveUnitSetup (f : Nat → Nat) (B : Nat) (mu nu P a r A A' : Ordinal.{0})
    (R t : Nat) : Prop :=
  SelectedWithThreshold f B ∧
  mu < epsilonZero ∧ nu < epsilonZero ∧ P < epsilonZero ∧ a < epsilonZero ∧
  A < epsilonZero ∧ A' < epsilonZero ∧
  (mu=0 ∨ Order.IsSuccLimit mu) ∧ (nu=0 ∨ Order.IsSuccLimit nu) ∧
  0 < P ∧ 2 ≤ a ∧ Ordinal.omega0^a ∣ P ∧ r < Ordinal.omega0^a ∧
  (r=0 ∨ Order.IsSuccLimit r) ∧
  20 ≤ R ∧ actualOrdinalNorm mu ≤ R ∧ actualOrdinalNorm nu ≤ R ∧
  actualOrdinalNorm P ≤ R ∧ actualOrdinalNorm a ≤ R ∧
  thickBlockTail R B ≤ t ∧
  actualLimitPart A = mu+(P+Ordinal.omega0^a+r) ∧
  actualLimitPart A' = nu+(P+Ordinal.omega0^a+r) ∧
  actualOrdinalNorm A=t ∧ actualOrdinalNorm A'=t ∧
  relativeProfile mu (Ordinal.log Ordinal.omega0 P) <
    relativeProfile nu (Ordinal.log Ordinal.omega0 P)

/-- Strict source sign paid on the original common clock, while the retained
prefix survives in both relative states. -/
def OrientedUnitDivergence (f : Nat → Nat) (mu nu P A A' : Ordinal.{0}) : Prop :=
  ∃ i : Nat,
    actualLimitPart ((descentWith f)^[i] A'-nu) < actualLimitPart ((descentWith f)^[i] A-mu) ∧
    P ≤ actualLimitPart ((descentWith f)^[i] A'-nu) ∧
    P ≤ actualLimitPart ((descentWith f)^[i] A-mu)

/-- Sensitive exponent >2: either immediate limit separation or a genuinely
created common thick block, both discharged internally. -/
def HigherSensitiveUnit : Prop := ∀ (f : Nat → Nat) (B : Nat)
    (mu nu P a r A A' : Ordinal.{0}) (R t : Nat),
  SensitiveUnitSetup f B mu nu P a r A A' R t → 2 < a →
  OrientedUnitDivergence f mu nu P A A'

/-- Exact single quadratic step at its actual top. This iff is separate from
arbitrary lower-suffix admission, which may already have diverged. -/
def QuadraticUnitTop : Prop := ∀ (f : Nat → Nat) (B : Nat)
    (mu nu P A A' : Ordinal.{0}) (R t : Nat),
  SensitiveUnitSetup f B mu nu P 2 0 A A' R t →
  (actualLimitPart (descentWith f A-mu) = actualLimitPart (descentWith f A'-nu) ↔
    relativeProfile nu (Ordinal.log Ordinal.omega0 P) =
      relativeProfile mu (Ordinal.log Ordinal.omega0 P)+1 ∧
    (relativeProfile mu (Ordinal.log Ordinal.omega0 P)+actualOrdinalNorm P)%2=1)

/-- Source-general quadratic admission: an earlier oriented divergence or the
literal single-sensitive-unit exception and actual synchronized continuation.
No supplied first hit, norm orbit, or common reset appears in the premises. -/
def QuadraticUnitAdmission : Prop := ∀ (f : Nat → Nat) (B : Nat)
    (mu nu P r A A' : Ordinal.{0}) (R t : Nat),
  SensitiveUnitSetup f B mu nu P 2 r A A' R t →
  OrientedUnitDivergence f mu nu P A A' ∨
  (relativeProfile nu (Ordinal.log Ordinal.omega0 P) =
      relativeProfile mu (Ordinal.log Ordinal.omega0 P)+1 ∧
   (relativeProfile mu (Ordinal.log Ordinal.omega0 P)+actualOrdinalNorm P)%2=1 ∧
   ∃ i k : Nat,
     FirstEntry f A (mu+(P+Ordinal.omega0^2)) i ∧
     FirstEntry f A' (nu+(P+Ordinal.omega0^2)) i ∧
     actualOrdinalNorm ((descentWith f)^[i+1] A)=f^[i+1] t ∧
     actualOrdinalNorm ((descentWith f)^[i+1] A')=f^[i+1] t ∧
     actualLimitPart ((descentWith f)^[i+1] A-mu)=P+Ordinal.omega0*(k : Ordinal) ∧
     actualLimitPart ((descentWith f)^[i+1] A'-nu)=P+Ordinal.omega0*(k : Ordinal))

def SensitiveUnitFoundation : Prop := HigherSensitiveUnit ∧ QuadraticUnitTop ∧ QuadraticUnitAdmission

end LogicLineages.PermittedControl.Targets
