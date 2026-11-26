module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyPutTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.Membership
open UniformCertificateCompletion Source
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalOriginalUniformParameterLeaves
open NumberedMultisetNumeric

/-- Encode the actual original raw primary-list entries injectively. This is
an implementation list, not a replacement primary relation or candidate pool. -/
def entriesCode {n : Nat} (xs : List (NumberedUniformPackedDecoding.RawPacked n)) : Nat :=
  numbersNumber (xs.map Encodable.encode)

/-- Original context/Object/packed decoding, then the unchanged original
finite primaryList. Every failed decode returns the original nil code. -/
def listValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun ctx obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map
      (fun q => entriesCode (ContextUniformPrimary.primaryList arity ctx.1.1 ctx.1.2 obj.1 q))).getD 0)
    (v.get 0) (v.get 1)

/-- Same original packed decoder for a candidate. The separate original T
guard below rejects failed decoding, so zero is never used as an Option tag. -/
def candidateValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2) : Nat :=
  decodedValue n (fun _ obj =>
    ((NumberedUniformPackedDecoding.rawPackedDecode n arity obj.1 obj.2).map Encodable.encode).getD 0)
    (v.get 0) (v.get 1)

def ListCalibrated (n : Nat) (arity : Fin n → Nat) (L : Program 2) : Prop :=
  ∀ v : List.Vector Nat 2, evaluate L v = listValue n arity v
def CandidateCalibrated (n : Nat) (arity : Fin n → Nat) (D : Program 2) : Prop :=
  ∀ v : List.Vector Nat 2, evaluate D v = candidateValue n arity v
def TargetCalibrated (n : Nat) (arity : Fin n → Nat) (T : Program 2) : Prop :=
  ∀ v : List.Vector Nat 2, evaluate T v = targetValue n arity v

/-- Inputs [head,tail-result,needle]. Exact equality selects one; otherwise
the literal recursive tail result is retained. No PR existence is used here. -/
def containsStep : Program 3 :=
  InternalAcceptance.branch
    (.composition InternalEqualityTest.equalityTest ![.projection 0,.projection 2])
    (.projection 1) (InternalLessThan.constantOne 3)
/-- Inputs [original numeric list code,needle]. -/
def contains : Program 2 :=
  InternalRawListRecursion.listRec (InternalAcceptance.constantZero 1) containsStep

/-- Inputs [seed,candidate,parameter]. Only the membership fold is transparent
in this first constructive component. L/D remain literal chosen subprograms,
and their internal graph correctness is not inferred from native calibration. -/
def classTest (T L D : Program 2) : Program 3 :=
  InternalAcceptance.conjunction
    (.composition T ![.projection 1,.projection 2])
    (.composition contains ![.composition L ![.projection 0,.projection 2],
      .composition D ![.projection 1,.projection 2]])

/-- Explicitly NEW initial tuple: install the exposed original primary-list
membership under the accepted bounded minimum. Never identify this AST with
the former existentially compiled representative. -/
def inputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (L D : Program 2) :=
  OriginalTransparentMinimum.minimumInputs H G (classTest (OriginalTypedDecoder.target H G) L D) p
def finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W L D : Program 2) :=
  SixSol20261113.Context.EvaluatorKeyPut.finalInputs (inputs p H G L D) H G W
    (classTest (OriginalTypedDecoder.target H G) L D)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TwoSol20261113.CalibratedPrimary.Membership
