module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderStepSpecification
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalVariableObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelection
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors (graph1)
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open UniformCertificateCompletion
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only the two original validity leaves change. The local membership AST
is derived from the SAME original member, never selected independently. -/
def transparentData (H G : Program 1) (W : Program 2) (data : Data) : Data :=
  { data with
    oldSource := OriginalUniverseDecoder.source H G
      (InternalOriginalUniformContextMembership.contextMember data.member) W
    oldTarget := OriginalTypedDecoder.target H G }

/-- One initial tuple is made transparent before any windows or runtime Gamma.
No representative, member, result, source presentation or final selector changes. -/
def transparentInputs (H G : Program 1) (W : Program 2)
    (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := transparentData H G W p.base }

/-- Literal identities, not equality of evaluations or an isomorphic tuple. -/
def PreservedFields (p q : GlobalSourcePackage.Inputs) : Prop :=
  q.base.oldRepresentative = p.base.oldRepresentative ∧
  q.base.member = p.base.member ∧ q.window = p.window ∧ q.oldSrc = p.oldSrc ∧
  q.oldComp = p.oldComp ∧ q.oldStep = p.oldStep ∧ q.oldVertex = p.oldVertex ∧
  q.oldResult = p.oldResult

/-- The original transparent leaves remain visible underneath exactly ONE
variable-leaf refinement. Every other initial field is literally unchanged. -/
def LiteralFields (p : GlobalSourcePackage.Inputs) (H G : Program 1)
    (W : Program 2) : Prop :=
  let q := transparentInputs H G W p
  let r := OriginalVariableLeaves.refineInputs G q
  q.base.oldSource = OriginalUniverseDecoder.source H G
      (InternalOriginalUniformContextMembership.contextMember p.base.member) W ∧
  q.base.oldTarget = OriginalTypedDecoder.target H G ∧ PreservedFields p q ∧
  r.base.oldSource = OriginalVariableLeaves.source
    (OriginalUniverseDecoder.source H G
      (InternalOriginalUniformContextMembership.contextMember p.base.member) W) p.base.member ∧
  r.base.oldTarget = OriginalVariableLeaves.target G (OriginalTypedDecoder.target H G) ∧
  PreservedFields p r

/-- Equality on EVERY raw input vector, including malformed contexts and
rejected syntax. The once-refined input remains calibrated, as does q itself. -/
def Calibration (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) : Prop :=
  let q := transparentInputs H G W p
  let r := OriginalVariableLeaves.refineInputs G q
  GlobalSourcePackage.InputsCalibrated n arity q ∧
  GlobalSourcePackage.InputsCalibrated n arity r ∧
  OriginalUniverseDecoder.ContextMemberCalibrated n
    (InternalOriginalUniformContextMembership.contextMember p.base.member) ∧
  (∀ v : List.Vector Nat 2,
    evaluate q.base.oldSource v = InternalOriginalUniformParameterLeaves.sourceValue n arity v ∧
    evaluate q.base.oldTarget v = InternalOriginalUniformParameterLeaves.targetValue n arity v ∧
    evaluate q.base.oldSource v = evaluate p.base.oldSource v ∧
    evaluate q.base.oldTarget v = evaluate p.base.oldTarget v ∧
    evaluate r.base.oldSource v = evaluate q.base.oldSource v ∧
    evaluate r.base.oldTarget v = evaluate q.base.oldTarget v)

/-- Complete preceding Object/canonical/weakening/native Properties, with the
entire original Package spelled out at the SAME unchanged final pipeline.
This universal property is rebuilt from its fields, without selecting q anew. -/
def Retained (n : Nat) (arity : Fin n → Nat) (q : GlobalSourcePackage.Inputs)
    (G : Program 1) : Prop :=
  OriginalFinalVariableObject.Properties n arity q G ∧
  GlobalSourcePackage.Package n arity
    (GlobalSourcePackage.source (OriginalLambdaTraversalSelection.finalInputs
      (OriginalVariableLeaves.refineInputs G q)))
    (GlobalSourcePackage.computability (OriginalLambdaTraversalSelection.finalInputs
      (OriginalVariableLeaves.refineInputs G q)))
    (GlobalSourcePackage.lift (OriginalLambdaTraversalSelection.finalInputs
      (OriginalVariableLeaves.refineInputs G q)))

/-- Native accepted reconstruction uses the original Context, Gamma, type and
codeNumber, with membership derived from this SAME selected original member. -/
def SourceReconstruction (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) (H : Program 1) (W : Program 2) : Prop :=
  ∀ typ raw gamma context : Nat,
    evaluate (OriginalUniverseDecoder.termCheck H
      (InternalOriginalUniformContextMembership.contextMember p.base.member) W)
      (List.Vector.ofFn ![typ,raw,gamma,context]) = 1 ↔
    ∃ (ctx : OrdinaryArithmeticQuotient.Context n) (Gamma : List Ty)
        (tau : Ty) (code : Code (Fin n)),
      Encodable.encode ctx = context ∧ Encodable.encode Gamma = gamma ∧
      typeNumber tau = typ ∧ codeNumber code = raw ∧
        NumberedUniverseRequests.valid arity ctx.1.1 ctx.1.2 (.term Gamma tau code) = true

/-- An independent local graph for the SAME selected H. This states no
whole-run transport, internal universe-step claim or internal I/C theorem. -/
def TypedStep (H : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type)
      (out input : OrdinaryArithmetic.Term alpha),
    Nonempty (Derivation body []
      ((graph1 (OriginalTypedDecoder.transition H) out input).iff
        (OriginalTypedDecoderStepSpecification.stepSpec H out input)))

/-- The original p, local H/G/W and all retained conclusions coexist before
any source windows, runtime contexts, raw inputs or internal symbolic terms.
The final input is always finalInputs (refineInputs G (transparentInputs H G W p)). -/
def Properties (n : Nat) (arity : Fin n → Nat) (p : GlobalSourcePackage.Inputs)
    (H G : Program 1) (W : Program 2) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity p ∧
  OriginalTypedDecoder.HeadSignatureCalibrated n arity H ∧
  OriginalVariableLeaves.ContextGuardCalibrated n G ∧
  OriginalUniverseDecoder.HeadWindowCalibrated n arity W ∧
  LiteralFields p H G W ∧ Calibration n arity p H G W ∧
  Retained n arity (transparentInputs H G W p) G ∧
  SourceReconstruction n arity p H W ∧ TypedStep H

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelection
