module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionTargets

open LogicLineages.OrdinalComparison (ordinalNaturalSum ordinalNaturalProduct)
open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent (PolicyShape)
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemantics
open AdmissibleSum DeterministicAccountData
open CurrentGroundConstruction CurrentGroundBudget
open CurrentUnaryChain (commonUnits)
open OriginalSecondBudget HeadFiniteSurplus

/-- Literal list, context and every pair of source/whole-vector payloads. -/
def ExactMergedPayloads : Prop :=
  ∀ (Γ : List Ty) (ops : List (Operator Γ)),
    NumericUnaryChain.contextCode (Γ.map SyntaxCode.typeCode) (ops.map operatorCode) =
      (context ops).map SyntaxCode.typeCode ∧
    (NumericUnaryChain.mergeData (ops.map operatorCode)).1 =
      (ops.map (fun op => op.privateContext.length)).sum ∧
    (NumericUnaryChain.mergeData (ops.map operatorCode)).2 = (merged ops).map NumericUnaryChain.pairCode

def ActualCaller : Prop :=
  ∀ (p : Policy) (Γ : List Ty) (k : Nat) (C : OriginalTerm Γ (Ty.curriedGround (k+1)))
    (u : OrdinalVector Γ (Ty.curriedGround (k+1)).level),
    AdmissibleAssignment.assignment p C = some u →
    ∃ v : OrdinalVector Γ 1,
      AdmissibleAssignment.assignment p (UnaryCarrier.saturate k C) = some v ∧
      v 1 = u (UnaryCarrier.headIndex k) ∧
      callerCode p (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode (Ty.curriedGround (k+1)))
        (SyntaxCode.encodeTerm C) = some (operatorCode (callerOp (UnaryCarrier.saturate k C) v))

def ExactSingleChain : Prop :=
  ∀ (p : Policy) (f : Nat → Nat) (Γ : List Ty) (ops : List (Operator Γ)),
    (∀ op ∈ ops, op.Assigned p) →
    CurrentUnaryChain.Assigned p (terms ops) (vectors ops) ∧
    ∃ v : OrdinalVector (context ops) 1,
      AdmissibleAssignment.assignment p (SourceUnaryChain.chainSource (terms ops)) = some v ∧
      chainCode p (Γ.map SyntaxCode.typeCode) (ops.map operatorCode) =
        some ((context ops).map SyntaxCode.typeCode,
          SyntaxCode.encodeTerm (SourceUnaryChain.chainSource (terms ops)),OrdinalSyntax.vectorCode v) ∧
      ∀ μ : Variable (context ops) .ground → Nat,
        ParametricSourceSuccessor.denoteWith f (commonUnits μ) (v 1) = chargedSum f ops

def ExactReplication : Prop :=
  ∀ (Γ : List Ty) (b : Nat) (xs : List (Operator Γ)) (caller : Operator Γ),
    (paidList b xs caller).length = scale b * xs.length + scale b ∧
    OriginalScaleCompilerCode.paidCode b (xs.map operatorCode) (operatorCode caller) =
      (paidList b xs caller).map operatorCode

/-- Independently checked finite/infinite ordinal accounting at the exact
original scale; all Nat subtractions in the declared remainder are paid. -/
def ExactPositiveGap : Prop :=
  ∀ (Γ : List Ty) (f : Nat → Nat) (b c : Nat) (xs : List (Operator Γ)) (caller : Operator Γ),
    4 ≤ b → 3*xs.length+4 ≤ c →
    0 < gap b xs.length c ∧ gap b xs.length c + 1 = scale b * (c-3*xs.length-3) ∧
    ordinalNaturalProduct (scale b : Ordinal)
      (ordinalNaturalSum
        ((xs.map (fun op => CurrentReserve.unitValue f (op.vector 1))).foldr ordinalNaturalSum 0
          + (c : Ordinal))
        (CurrentReserve.unitValue f (caller.vector 1))) =
      chargedSum f (paidList b xs caller) + (gap b xs.length c : Ordinal)

/-- Exact conclusion for the original literal P and C. The two actual
original assignments and actual original full-box coordinate are retained.
Later graph emission may use a different paid certificate; that is not this
positive-remainder construction. -/
def SourceResult (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
    (P : OriginalTerm (Ty.curriedGround (k+1) :: Γ) .ground)
    (C : OriginalTerm Γ (Ty.curriedGround (k+1))) : Prop :=
  ∃ (u : OrdinalVector (Ty.curriedGround (k+1) :: Γ) 0)
    (B : OrdinalVector Γ (Ty.arrow (Ty.curriedGround (k+1)) Ty.ground).level)
    (caller : OrdinalVector Γ (Ty.curriedGround (k+1)).level)
    (v : OrdinalPartialVector Γ (Ty.curriedGround (k+1)))
    (rs : List (UnaryRecord (Ty.curriedGround (k+1) :: Ty.curriedGround (k+1) :: Γ)))
    (xs : List (CurrentReserve.Carrier p)) (vC : OrdinalVector Γ 1) (b c : Nat),
    AdmissibleAssignment.assignment p P = some u ∧
    AdmissibleAssignment.assignment p (.lam P) = some B ∧
    AdmissibleAssignment.assignment p C = some caller ∧
    AdmissiblePartial.run p 0 (u 0) = some v ∧
    CurrentReserve.SpawnedAccount p f (u 0) xs c ∧ List.Forall₂ CurrentGroundAccount.Matches rs xs ∧
    (4 : Int) ≤ CurrentReserve.reserve xs c ∧
    CurrentGroundAccount.sourceCode p ((Ty.curriedGround (k+1) :: Γ).map SyntaxCode.typeCode)
      (SyntaxCode.encodeTerm P) = some (OrdinalSyntax.vectorCode u,rs.map CurrentGroundAccount.recordCode,c) ∧
    B (boxFirst k) = v (outputOne k) ∧ B (boxSecond k) = v (outputTwo k) ∧
    b = scalarSecond (u 0) ∧ 4 ≤ b ∧
    AdmissibleAssignment.box p B caller (boxSecond k) = B (boxSecond k) ∧
    (∀ ν : OrdinalComponent Γ → Ordinal,
      ParametricSourceSuccessor.denoteWith f ν (B (boxSecond k)) = (b : Ordinal)) ∧
    AdmissibleAssignment.assignment p (UnaryCarrier.saturate k C) = some vC ∧
    vC 1 = caller (UnaryCarrier.headIndex k) ∧
    let ops := paidList b (rs.map carrierOp) (callerOp (UnaryCarrier.saturate k C) vC)
    let K := SourceUnaryChain.chainSource (terms ops)
    ∃ (w : OrdinalVector (context ops) 1) (Δ : Nat),
      AdmissibleAssignment.assignment p K = some w ∧
      compileCode p (Γ.map SyntaxCode.typeCode) (SyntaxCode.typeCode (Ty.curriedGround (k+1)))
        (SyntaxCode.encodeTerm P) (SyntaxCode.encodeTerm C) =
          some (((context ops).map SyntaxCode.typeCode,SyntaxCode.encodeTerm K,OrdinalSyntax.vectorCode w),b,Δ) ∧
      Δ = gap b rs.length c ∧ 0 < Δ ∧
      ∀ (ρ : Variable Γ .ground → Nat) (μ : Variable (context ops) .ground → Nat),
        ordinalNaturalProduct (scale b : Ordinal)
          (ordinalNaturalSum
            (ParametricSourceSuccessor.denoteWith f (commonUnits ρ) (B (boxFirst k)))
            (ParametricSourceSuccessor.denoteWith f (commonUnits ρ) (caller (UnaryCarrier.headIndex k)))) =
          ParametricSourceSuccessor.denoteWith f (commonUnits μ) (w 1) + (Δ : Ordinal)

/-- Neither a child certificate, numeric bound nor an annotation is a
hypothesis. Both the typed witness and the literal generated-source domains
are stated; the latter uses actual original free-name membership. -/
def ActualOriginalConstruction : Prop :=
  (∀ (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
      (P : TrackedSource.Expr k (Ty.curriedGround (k+1) :: Γ) .here 0)
      (C : OriginalTerm Γ (Ty.curriedGround (k+1))),
    TrackedSource.active P = true → SourceResult p f k Γ (TrackedSource.erase P) C) ∧
  (∀ (p : Policy) (f : Nat → Nat) (k : Nat) (Γ : List Ty)
      (P : OriginalTerm (Ty.curriedGround (k+1) :: Γ) .ground)
      (C : OriginalTerm Γ (Ty.curriedGround (k+1))),
    @TrackedSource.Generated k (Ty.curriedGround (k+1) :: Γ) .here 0 P →
    (⟨Ty.curriedGround (k+1),.here⟩ : SourceFreeOccurrences.PackedVariable _) ∈
      SourceFreeOccurrences.freeOccurrences P →
    SourceResult p f k Γ P C)

/-- Only the policy selector is an effectivity parameter. f is not queried
by the code: generated positive fields do not contain collapse. -/
def AlgorithmsEffective : Prop :=
  ∀ p : Policy, PolicyShape.Effective p →
    Computable (fun z : List Nat × Nat × Nat => callerCode p z.1 z.2.1 z.2.2) ∧
    Computable (fun z : List Nat × List NumericUnaryChain.RawOperator => chainCode p z.1 z.2) ∧
    Computable (fun z : List Nat × Nat × Nat × Nat => compileCode p z.1 z.2.1 z.2.2.1 z.2.2.2)

/-- Whole numbered scope and the source-exact supporting contracts. -/
def Full : Prop :=
  CurrentGroundBudgetTargets.Full ∧ CurrentGroundAnnotationTargets.Full ∧ CurrentGroundAccountTargets.Full ∧
    ExactMergedPayloads ∧ ActualCaller ∧ ExactSingleChain ∧ ExactReplication ∧ ExactPositiveGap ∧
    ActualOriginalConstruction ∧ AlgorithmsEffective

end LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionTargets
