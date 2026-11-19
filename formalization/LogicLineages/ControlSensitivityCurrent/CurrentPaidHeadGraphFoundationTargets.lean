module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphFoundationDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.Targets

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleAssignment AdmissibleSum ForwardTranslation
open ParametricSourceSuccessor
open CurrentUnaryChain (commonUnits)

/-- The exact current-f norm-affordable maximum, not a fixed-G predecessor
and not a supplied equality of collapse values. -/
def ExactStep : Prop :=
  ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (μ : Ordinal), μ < epsilonZero → Order.IsSuccLimit μ →
    μ + Ordinal.omega0 < epsilonZero ∧ Order.IsSuccLimit (μ+Ordinal.omega0) ∧
    actualOrdinalNorm (μ+Ordinal.omega0) = actualOrdinalNorm μ+2 ∧
    ∀ t : Nat, actualOrdinalNorm (μ+Ordinal.omega0) ≤ t →
      actualMaximumPredecessor (μ+Ordinal.omega0) (f t) = actualHeadInitial μ (f t) ∧
      J f (μ+Ordinal.omega0) t = J f μ (f t)+1

/-- All offsets including Δ=0; the induction is upward in f and retains
its domain conditions all the way down to β. -/
def ExactIteration : Prop :=
  ∀ (f : Nat → Nat), FullAddition.Targets.SourceGrowth f →
  ∀ (β : Ordinal), β < epsilonZero → Order.IsSuccLimit β → ∀ Δ : Nat,
    shiftHead β Δ < epsilonZero ∧ Order.IsSuccLimit (shiftHead β Δ) ∧
    actualOrdinalNorm (shiftHead β Δ) = actualOrdinalNorm β+2*Δ ∧
    ∀ t : Nat, actualOrdinalNorm (shiftHead β Δ) ≤ t →
      actualOrdinalNorm β ≤ (f^[Δ]) t ∧ J f (shiftHead β Δ) t = J f β ((f^[Δ]) t)+Δ

/-- At genuine positive encoded ground valuations the original full-box
coordinate and paid positive fields keep the original same joint inputs. The
original BC scalar uses the actual level contribution and not the ray scalar. -/
def ExactOriginalPayment : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (Γ Ξ : List Ty) (σ τ : Ty)
    (B : OriginalTerm Γ (.arrow σ τ)) (C : OriginalTerm Γ σ)
    (K : OriginalTerm Ξ (Ty.curriedGround 1)) (b Δ : Nat) (h : Paid p f B C K b Δ),
    h.baseHead < epsilonZero ∧ Order.IsSuccLimit h.baseHead ∧
    h.paidHead = shiftHead h.baseHead Δ ∧
    ∀ (ρ : Variable Γ .ground → Nat),
      denoteWith f (commonUnits ρ) (box p h.Bvector h.Cvector (boxSecond σ τ h.callerLevel)) =
        (b : Ordinal) ∧
      denoteWith f (commonUnits ρ) (box p h.Bvector h.Cvector (sourceFirst σ τ)) =
        ordinalNaturalProduct ((2^b : Nat) : Ordinal)
          (ordinalNaturalSum (denoteWith f (commonUnits ρ) (h.Bvector (sourceFirst σ τ)))
            (denoteWith f (commonUnits ρ) (h.Cvector (callerFirst σ h.callerLevel)))) ∧
      ∀ (B₀ C₀ y : Nat),
        CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) B B₀ →
        CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) C C₀ →
        (CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (.app B C) y ↔
          y = J f h.paidHead (actualOrdinalNorm h.paidHead+B₀+C₀+σ.level))

/-- Disjoint typed ground ranks and exact raw layout, including preservation
of every actual functional slot in the auxiliary scope. -/
def ExactFreshAuxiliary : Prop :=
  (∀ Γ : List Ty,
    Function.Injective (fun x : Variable Γ .ground => freshRename Γ x) ∧
    (∀ x : Variable Γ .ground,
      RawSourceDAG.variableIndex (freshRename Γ x) < (CurrentUnitElimination.groundCtx Γ).length) ∧
    (∀ (σ τ : Ty) (x : Variable Γ (.arrow σ τ)),
      RawSourceDAG.variableIndex (freshRename Γ x) =
        (CurrentUnitElimination.groundCtx Γ).length + RawSourceDAG.variableIndex x)) ∧
  ∀ (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)),
    (∀ x : Variable (FreshCtx Γ) .ground,
      (⟨Ty.ground,x⟩ : SourceFreeOccurrences.PackedVariable (FreshCtx Γ)) ∉
        SourceFreeOccurrences.freeOccurrences (zeroCopy K)) ∧
    auxiliaryCode (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) =
      some (((.ground :: FreshCtx Γ) : List Ty).map SyntaxCode.typeCode,
        SyntaxCode.encodeTerm (raySource K))

/-- The actual current assignment of the freshly renamed, ground-zeroed
auxiliary K supplies both the unchanged head and its real scalar c. The
new application uses raw z₀=n+1 with every other ground slot arbitrary. -/
def ExactRay : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1))
    (u : OrdinalVector Γ 1), assignment p K = some u →
    ∃ (c : Nat) (w : OrdinalVector (FreshCtx Γ) 1),
      assignment p (zeroCopy K) = some w ∧ atUnits f (u 0) = (c : Ordinal) ∧
      (∀ μ : Variable (FreshCtx Γ) .ground → Nat,
        denoteWith f (commonUnits μ) (w 1) = atUnits f (u 1) ∧
        denoteWith f (commonUnits μ) (w 0) = (c : Ordinal)) ∧
      ∀ (ρ : Variable (.ground :: FreshCtx Γ) .ground → Nat) (v : Nat),
        CurrentAbsolute.Scalar p f (ExistentialPlan.inputs ρ) (raySource K) v ↔
        v = J f (ordinalNaturalProduct Ordinal.omega0 (atUnits f (u 1)))
          (RayBase (ordinalNaturalProduct Ordinal.omega0 (atUnits f (u 1))) c + ρ .here)

/-- Literal normal-note codes, actual source scalar, norms and exact closed
J evaluator on every genuine guarded input. Malformed code behavior is not
used as evidence about any source. -/
def ExactParameters : Prop :=
  ∀ (p : Policy) (f : Nat → Nat), Computable f → FullAddition.Targets.SourceGrowth f →
  ∀ (Γ : List Ty) (K : OriginalTerm Γ (Ty.curriedGround 1)) (u : OrdinalVector Γ 1),
    assignment p K = some u → ∀ δ : Nat,
    ∃ (β ξ : NONote) (c : Nat),
      let beta := ordinalNaturalProduct Ordinal.omega0 (atUnits f (u 1))
      parameterCode p f (Γ.map SyntaxCode.typeCode) (SyntaxCode.encodeTerm K) δ =
        some (rawNoteEncode β.1,rawNoteEncode ξ.1,c) ∧
      β.1.repr = beta ∧ ξ.1.repr = shiftHead beta δ ∧ atUnits f (u 0) = (c : Ordinal) ∧
      rawNormCode (rawNoteEncode β.1) = actualOrdinalNorm beta ∧
      rawNormCode (rawNoteEncode ξ.1) = actualOrdinalNorm (shiftHead beta δ) ∧
      ∀ t : Nat, actualOrdinalNorm (shiftHead beta δ) ≤ t →
        valueCode f (rawNoteEncode ξ.1) t = J f (shiftHead beta δ) t

def EffectivePrefixData : Prop :=
  Computable (fun d : List Nat × Nat => auxiliaryCode d.1 d.2) ∧
  ∀ (p : Policy), PolicyShape.Effective p → ∀ (f : Nat → Nat),
    Computable f → FullAddition.Targets.SourceGrowth f →
    Computable (fun d : List Nat × Nat × Nat => parameterCode p f d.1 d.2.1 d.2.2) ∧
    Computable (fun d : Nat × Nat => valueCode f d.1 d.2)

def Foundation : Prop := ExactStep ∧ ExactIteration ∧ ExactOriginalPayment ∧
  ExactFreshAuxiliary ∧ ExactRay ∧ ExactParameters ∧ EffectivePrefixData

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph.Targets
