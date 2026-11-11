module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentative
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors (graph1 graph2)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Compare the actual all-variable-occurrence ranks of the candidate and
input, using the original literal raw packed-rank Program. -/
def sameRank (R : Program 2) : Program 2 :=
  InternalApplicationStepPeel.same
    (.composition OriginalRawSyntaxTransport.variableRankPackedRaw (fun _ : Fin 1 => R))
    (.composition OriginalRawSyntaxTransport.variableRankPackedRaw
      (fun _ : Fin 1 => .projection 0))

/-- BOTH existing window acceptance and the supplied transparent source
acceptance activate the guard. No representative occurs in this test. -/
def active (source : Program 2) (window : Program 1) : Program 2 :=
  InternalAcceptance.conjunction (BottomRepresentative.windowAt window) source

/-- Keep the whole old representative when either original guard rejects.
On active inputs retain only same-rank candidates, otherwise return the raw
input. The native redundancy of that fallback is an obligation. -/
def representative (source R : Program 2) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch (active source window) R
    (InternalAcceptance.branch (sameRank R) (.projection 0) R)

/-- Replace only the INITIAL representative. Its source test is the actual
transparent decoder, not the opaque oldSource of p. The decoder depends on
p.member and not on p.oldRepresentative, so the construction is acyclic. -/
def guardedInputs (H G : Program 1) (W : Program 2)
    (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  let q := OriginalTransparentDecoderSelection.transparentInputs H G W p
  { p with base := { p.base with oldRepresentative := representative q.base.oldSource p.base.oldRepresentative p.window } }

/-- Apply the unchanged transparent selection AFTER the initial guard.
This is the initial tuple for the SAME once-refined final pipeline. -/
def transparentInputs (H G : Program 1) (W : Program 2)
    (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalTransparentDecoderSelection.transparentInputs H G W (guardedInputs H G W p)

def LiteralFields (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  let s := guardedInputs H G W p
  let q := transparentInputs H G W p
  s.base.oldSource = p.base.oldSource ∧ s.base.oldTarget = p.base.oldTarget ∧
  s.base.member = p.base.member ∧ s.window = p.window ∧ s.oldSrc = p.oldSrc ∧
  s.oldComp = p.oldComp ∧ s.oldStep = p.oldStep ∧ s.oldVertex = p.oldVertex ∧
  s.oldResult = p.oldResult ∧
  q.base.oldSource = (OriginalTransparentDecoderSelection.transparentInputs H G W p).base.oldSource ∧
  q.base.oldRepresentative = representative q.base.oldSource p.base.oldRepresentative p.window

/-- Equality on EVERY input vector, including malformed decodes and
nonclosed windows; those inactive cases retain the whole original output. -/
def NativePreparation (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  (∀ v : List.Vector Nat 2,
    evaluate (guardedInputs H G W p).base.oldRepresentative v =
      evaluate p.base.oldRepresentative v) ∧
  GlobalSourcePackage.InputsCalibrated n arity (guardedInputs H G W p)

/-- Independent internal rank preservation at the actual guarded INITIAL
representative and actual transparent source. BOTH original window and source
acceptance are explicit. No full-fold, cancellation or I/C law is asserted. -/
def RankLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out input parameter rank : OTerm alpha),
  let q := transparentInputs H G W p
  Nonempty (Derivation body Delta
    ((graph2 (BottomRepresentative.windowAt q.window) InternalOriginalStepGuard.one input parameter ⊓
      (graph2 q.base.oldSource InternalOriginalStepGuard.one input parameter ⊓
        graph2 q.base.oldRepresentative out input parameter)).imp
      ((graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank out).iff
        (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw rank input))))

/-- Rebuild the COMPLETE existing transparent-selection Properties, including
its original retained Properties and explicit full Package, at the guarded
initial tuple. The once-refined finalInputs/finalData pipeline is unchanged. -/
def Retained (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  OriginalTransparentDecoderSelection.Properties n arity (guardedInputs H G W p) H G W

def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  OriginalTransparentDecoderSelection.Properties n arity p H G W ∧
  LiteralFields p H G W ∧ NativePreparation n arity p H G W ∧
  RankLaw p H G W ∧ Retained n arity p H G W

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRankGuardedRepresentative
