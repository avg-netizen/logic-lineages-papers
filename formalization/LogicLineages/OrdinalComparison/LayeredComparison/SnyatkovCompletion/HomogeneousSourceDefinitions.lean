module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceFormulaCodecDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSource

def peelExists : SourceFormula → List Nat × SourceFormula
  | .existsNat i p => let q := peelExists p; (i :: q.1, q.2)
  | p => ([], p)

/-- Recognize the literal source encoding of a universal binder only. -/
def peelForall : SourceFormula → List Nat × SourceFormula
  | .negative (.existsNat i (.negative p)) => let q := peelForall p; (i :: q.1, q.2)
  | p => ([], p)

def admissible (p : SourceFormula) : Bool :=
  SourceBooleanGraph.test (peelExists p).2 || SourceBooleanGraph.test (peelForall p).2

def decide (values : List Nat) (p : SourceFormula) : Option Bool :=
  let e := peelExists p
  if SourceBooleanGraph.test e.2 then SourceParameterDecision.decideExists e.1 values e.2
  else let a := peelForall p; SourceParameterDecision.decideForall a.1 values a.2

namespace Code
def peelExists (code : Nat) : List Nat × Nat :=
  if code % 5 = 4 then
    let p := peelExists (code / 5).unpair.2
    ((code / 5).unpair.1 :: p.1, p.2)
  else ([], code)
termination_by code
decreasing_by
  have hpos : 0 < code := by omega
  have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
  exact lt_of_le_of_lt (Nat.unpair_right_le _) hd

def forallTest (code : Nat) : Prop :=
  code % 5 = 2 ∧ (code / 5) % 5 = 4 ∧ ((code / 5 / 5).unpair.2) % 5 = 2
instance (code : Nat) : Decidable (forallTest code) := inferInstanceAs (Decidable (_ ∧ _ ∧ _))
def forallName (code : Nat) : Nat := (code / 5 / 5).unpair.1
def forallChild (code : Nat) : Nat := (code / 5 / 5).unpair.2 / 5

def peelForall (code : Nat) : List Nat × Nat :=
  if forallTest code then
    let p := peelForall (forallChild code)
    (forallName code :: p.1, p.2)
  else ([], code)
termination_by code
decreasing_by
  have hpos : 0 < code := by unfold forallTest at *; omega
  have hd : code / 5 < code := Nat.div_lt_self hpos (by decide)
  have hq := Nat.div_le_self (code / 5) 5
  have hr := Nat.unpair_right_le (code / 5 / 5)
  have hc := Nat.div_le_self (code / 5 / 5).unpair.2 5
  unfold forallChild
  omega

def admissible (code : Nat) : Bool :=
  SourceBooleanPrograms.Code.test (peelExists code).2 || SourceBooleanPrograms.Code.test (peelForall code).2

def decide (values : List Nat) (code : Nat) : Option Bool :=
  let e := peelExists code
  if SourceBooleanPrograms.Code.test e.2 then SourceParameterDecision.Code.decideExists e.1 values e.2
  else let a := peelForall code; SourceParameterDecision.Code.decideForall a.1 values a.2
end Code

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSource
