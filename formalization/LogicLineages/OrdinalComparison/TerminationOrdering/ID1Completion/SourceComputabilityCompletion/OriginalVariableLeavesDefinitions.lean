module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalNativeAccessibilityDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformContextMembershipDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeaves
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL outer Context decoder, including rejection on malformed
finite-table codes. This guard does not inspect or capture a runtime Gamma. -/
def ContextGuardCalibrated (n : Nat) (guard : Program 1) : Prop :=
  ∀ v : List.Vector Nat 1, evaluate guard v =
    (Encodable.decode (α := OrdinaryArithmeticQuotient.Context n) (v.get 0)).isSome.toNat

/-- Original raw packed type and de Bruijn index; Gamma retains its original
Encodable list code in the right coordinate of the unchanged parameter. -/
def variableCheck : Program 2 :=
  .composition OriginalVariableDecoder.check
    ![leftOf (.projection 0),rightOf (rightOf (.projection 0)),rightOf (.projection 1)]

def variableTag : Program 2 :=
  .composition OriginalConstructorLeaf.variableTest (fun _ : Fin 1 => .projection 0)

def contextCheck (guard : Program 1) : Program 2 :=
  .composition guard (fun _ : Fin 1 => leftOf (.projection 1))

def typeMember (member : Program 2) : Program 2 :=
  .composition (InternalOriginalUniformContextMembership.normalizedMember member)
    ![leftOf (.projection 0),.projection 1]

/-- Source variables need the original finite type window as well as the
original dependent variable decoder. Normalization changes only Gamma input
to membership, whose independence is a separate proved native supplier. -/
def sourceVariable (member : Program 2) : Program 2 :=
  InternalAcceptance.conjunction (typeMember member) variableCheck

/-- Target variables still reject malformed ORIGINAL outer contexts. Dropping
this factor would break all-vector equality even when Gamma/index are valid. -/
def targetVariable (guard : Program 1) : Program 2 :=
  InternalAcceptance.conjunction (contextCheck guard) variableCheck

/-- Branch order is control, zero branch, nonzero branch. Every nonvariable
branch retains the whole old leaf literally, including malformed inputs. -/
def source (oldSource member : Program 2) : Program 2 :=
  InternalAcceptance.branch variableTag oldSource (sourceVariable member)

def target (guard : Program 1) (oldTarget : Program 2) : Program 2 :=
  InternalAcceptance.branch variableTag oldTarget (targetVariable guard)

/-- Refine only the variable-tag source/target branches ONCE, before windows
and runtime Gamma. Representative/member remain the identical old Programs. -/
def refineData (guard : Program 1) (data : Data) : Data :=
  { data with
    oldSource := source data.oldSource data.member
    oldTarget := target guard data.oldTarget }

def refineInputs (guard : Program 1) (p : GlobalSourcePackage.Inputs) :
    GlobalSourcePackage.Inputs :=
  { p with base := refineData guard p.base }

/-- All-output arithmetic exposure at the literal original variable-tag
guard. The concrete branch ASTs call OriginalVariableDecoder.check at the
actual type/index/Encodable-Gamma selectors; no semantic reflection or
transformed-input acceptance is assumed. -/
def BranchLaws (guard : Program 1) (data : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 variableTag InternalOriginalStepGuard.one raw parameter).imp
      (((graph2 (refineData guard data).oldSource out raw parameter).iff
          (graph2 (sourceVariable data.member) out raw parameter)) ⊓
        ((graph2 (refineData guard data).oldTarget out raw parameter).iff
          (graph2 (targetVariable guard) out raw parameter)))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalVariableLeaves
