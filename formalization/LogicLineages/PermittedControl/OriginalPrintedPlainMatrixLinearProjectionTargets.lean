module
public import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaTargets
public import LogicLineages.PermittedControl.OriginalNormalizedMatrixPositiveSnapshotsTargets
public import LogicLineages.PermittedControl.OriginalMatrixActualHighPacketTargets

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OriginalPrintedCircuitSequential (Gate)
open ActualFiniteOrderBranches (Pattern guard rename realized)
open OriginalPrintedPlainMatrixOrderBranches (branches renamed SourceAccepts)
open OriginalPrintedPlainMatrixInfiniteLow (circuit matrix)
open OriginalNormalizedCircuitMatrix (rowsList)
open OriginalMatrixDenseRanks (support renameRow)
open OriginalMatrixLinearLowerTable (TopLinear lowerTable Live assignment)
open OriginalMatrixLinearRowFormula (rowFormula choosePolarity)
open PreparedProjection (PreparedInput PreparedTableTied eliminatePreparedFormula)
open HeterogeneousSignedMatrixSlice (Row)

def top (branch : Pattern) : Nat := branch.1 - 1

noncomputable def replay (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) (z name : Nat) : Nat :=
  if name ∈ support (matrix known gates p) ∧ rename branch name = top branch then z else θ name

noncomputable def table (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) : List PreparedProjection.LowerOperand :=
  lowerTable (top branch) (renamed known gates p branch)

def atomMap (atom : NormalForm.Atom → NormalForm.Formula) : NormalForm.Formula → NormalForm.Formula
  | .truth => .truth
  | .falsity => .falsity
  | .atom a => atom a
  | .negative p => .negative (atomMap atom p)
  | .conjunction p q => .conjunction (atomMap atom p) (atomMap atom q)
  | .disjunction p q => .disjunction (atomMap atom p) (atomMap atom q)

def conjoin (ps : List NormalForm.Formula) : NormalForm.Formula :=
  ps.foldr NormalForm.Formula.conjunction .truth

def lowerBound (n : Nat) : NormalForm.Formula :=
  .atom (.nonnegative (-(n : Int),[(1,.variable 0)]))

noncomputable def safeMinimum (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate)
    (p : NormalForm.Formula) (branch : Pattern) : Nat :=
  max (OriginalMatrixActualHighPacket.originalFamilyCeiling B known gates p)
    (if top branch = 0 then 0 else realized θ branch (top branch - 1) + 1)

/-- Literal order row tests are compiled over one actual lower table.
The terminal retains its full Boolean syntax, with polarity outside it,
and the entire computational prefix remains a positive conjunction. -/
noncomputable def formula (known : List Nat) (gates : List Gate) (p : NormalForm.Formula)
    (branch : Pattern) (minimum : Nat) (positive : Bool) : NormalForm.Formula :=
  let compile := fun row => rowFormula (top branch) (table known gates p branch) (renameRow (rename branch) row)
  .conjunction (lowerBound minimum)
    (.conjunction (conjoin ((rowsList (circuit known gates p)).map compile))
      (choosePolarity (atomMap (fun a => compile (OriginalPlainTerminalMatrix.atomRow a)) p) positive))

def ExactAlreadyLinearPreparedCircuit : Prop :=
  ∀ (f θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      TopLinear (top branch) (renamed known gates p branch) →
      ∀ (minimum : Nat) (positive : Bool),
        let ops := table known gates p branch
        let q := formula known gates p branch minimum positive
        PreparedInput ops q ∧
        ∀ (ν : Nat → Nat), PreparedTableTied f (top branch) (realized θ branch) ops ν →
          ∀ z : Nat, q.eval (Function.update ν 0 z) ↔
            minimum ≤ z ∧ SourceAccepts f (replay θ known gates p branch z) known gates p positive

/-- Project only the already-linear greatest rank, with its exact tied
actual lower tape. The supported outer prior is independent of updates
to the greatest equality class; it is never passed to Presburger. -/
def ExactAlreadyLinearCircuitProjection : Prop :=
  ∀ (f θ : Nat → Nat) (B : Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    PreparedProjection.PlainPreparedFormula p →
    ∀ branch ∈ branches known gates p, (guard branch).eval θ → 0 < branch.1 →
      TopLinear (top branch) (renamed known gates p branch) →
      ∀ (prior : (Nat → Nat) → Prop) (positive : Bool),
        (∀ z : Nat, prior (replay θ known gates p branch z) ↔ prior θ) →
        ((let ops := table known gates p branch
          let q := formula known gates p branch (safeMinimum B θ known gates p branch) positive
          prior θ ∧ Live f (realized θ branch) ops ∧
            (eliminatePreparedFormula q).eval (assignment f (realized θ branch) ops)) ↔
          ∃ z : Nat, safeMinimum B θ known gates p branch ≤ z ∧
            prior (replay θ known gates p branch z) ∧
            SourceAccepts f (replay θ known gates p branch z) known gates p positive)

def ExactGreatestReplayGuards : Prop :=
  ∀ (B : Nat) (θ : Nat → Nat) (known : List Nat) (gates : List Gate) (p : NormalForm.Formula),
    ∀ branch ∈ branches known gates p, (guard branch).eval θ →
      ∀ z : Nat, safeMinimum B θ known gates p branch ≤ z →
        (guard branch).eval (replay θ known gates p branch z) ∧
        ((∀ name ∈ support (matrix known gates p),
          OriginalMatrixActualHighPacket.originalFamilyCeiling B known gates p ≤ θ name) →
          ∀ name ∈ support (matrix known gates p),
            OriginalMatrixActualHighPacket.originalFamilyCeiling B known gates p ≤
              replay θ known gates p branch z name)

def FullOriginalPrintedPlainMatrixLinearProjection : Prop :=
  ExactAlreadyLinearPreparedCircuit ∧ ExactAlreadyLinearCircuitProjection ∧ ExactGreatestReplayGuards

end LogicLineages.PermittedControl.OriginalPrintedPlainMatrixLinearProjection
