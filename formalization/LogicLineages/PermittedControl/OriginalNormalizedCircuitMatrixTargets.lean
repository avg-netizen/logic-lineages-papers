module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNormalizationTargets
public import LogicLineages.PermittedControl.OriginalFieldGateMatrixTargets
public import LogicLineages.PermittedControl.AffineCollapseGuardedLowTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrix
open OrdinalComparison
open ArbitraryHeadSharedWire (Valuation)
open NaturalAffineGateGraph (Expression)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open ArbitraryHeadWireList (NormalGate)
open OriginalPrintedCircuitNormalization (NormalizedGate Holds normalized)

def affineRows (e : Expression) (out : Nat) : List Row :=
  [(.equalZero,e.1,AffineCollapseGuardRows.affineTerms e out)]

def failedRows : List Row := [(.equalZero,1,[])]

def LimitHead (head : Nat) : Prop :=
  ONote.NF (rawNoteDecode head) ∧ Order.IsSuccLimit (rawNoteDecode head).repr

def typedHead (head : Nat) (h : LimitHead head) : NONote :=
  ⟨rawNoteDecode head,h.1⟩

/-- An invalid raw limit head is not converted to a successful field.
It gives one literal always-failing row. -/
noncomputable def limitRows (head : Nat) (e : Expression) (i o : Nat) : List Row :=
  @dite (List Row) (LimitHead head) (Classical.propDecidable _)
    (fun h => AffineCollapseGuardRows.guardRows (typedHead head h) e i o)
    (fun _ => failedRows)

noncomputable def limitPassing (θ : Valuation) (head i : Nat) : Snapshot :=
  @dite Snapshot (LimitHead head) (Classical.propDecidable _)
    (fun h => AffineCollapseGuardedLow.originalGuardSnapshot (typedHead head h) i θ)
    (fun _ => [(0,true)])

noncomputable def baseRows : NormalGate → List Row
  | .affine e o => affineRows e o
  | .limitPair head e i o => limitRows head e i o

noncomputable def basePassing (θ : Valuation) : NormalGate → Snapshot
  | .affine .. => [(0,true)]
  | .limitPair head _ i _ => limitPassing θ head i

noncomputable def rows : NormalizedGate → List Row
  | .base g => baseRows g
  | .field g => OriginalFieldGateMatrix.rows g

noncomputable def passing (θ : Valuation) : NormalizedGate → Snapshot
  | .base g => basePassing θ g
  | .field g => OriginalFieldGateMatrix.passing θ g

noncomputable def rowsList (gates : List NormalizedGate) : List Row := gates.flatMap rows
noncomputable def passingList (θ : Valuation) (gates : List NormalizedGate) : Snapshot :=
  gates.flatMap (passing θ)

def ExactNormalizedBaseRows : Prop :=
  ∀ (f : Nat → Nat) (θ : Valuation) (g : NormalGate),
    (baseRows g).length = (basePassing θ g).length ∧
      (actualRows f θ (baseRows g) (basePassing θ g) ↔ g.Holds f θ)

def ExactNormalizedCircuitRows : Prop :=
  ∀ (f : Nat → Nat) (θ : Valuation) (gates : List NormalizedGate),
    (rowsList gates).length = (passingList θ gates).length ∧
      (actualRows f θ (rowsList gates) (passingList θ gates) ↔ Holds f θ gates)

def ExactPrintedNormalizedMatrix : Prop :=
  ∀ (f : Nat → Nat) (θ : Valuation) (ext : Nat) (gates : List OriginalPrintedCircuitSequential.Gate),
    actualRows f θ (rowsList (normalized ext gates)) (passingList θ (normalized ext gates)) ↔
      Holds f θ (normalized ext gates)

def FullOriginalNormalizedCircuitMatrix : Prop :=
  ExactNormalizedBaseRows ∧ ExactNormalizedCircuitRows ∧ ExactPrintedNormalizedMatrix

end LogicLineages.PermittedControl.OriginalNormalizedCircuitMatrix
