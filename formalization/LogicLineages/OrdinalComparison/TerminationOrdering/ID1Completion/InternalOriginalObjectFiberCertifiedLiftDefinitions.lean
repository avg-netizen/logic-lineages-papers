module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberSourceAssemblyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalComputabilityDownwardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLift
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open SourceComputabilityFormulaSupportProof NumberedLeastCodeRepresentative
open InternalApplicationCertificateConstructors
open InternalOriginalObjectFiberSourceAssembly
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ONLY additional premise of the fiber-qualified certified lift. This
is an actual original Program graph, not a semantic Object decoder equality. -/
def argumentFiber {α : Type} (Gamma : List Ty) (a : OTerm α) : Formula α :=
  graph1 InternalUnpair.left (numeral (Encodable.encode Gamma)) a

/-- The antecedent of InternalComputabilityDownward.CertifiedApplicationLift,
with its original conjunction tree, inputs, certificate and outputs unchanged. -/
def originalPremises {α : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (lift : Program 5) (context : Nat)
    (sigma tau : Ty) (f g a out other witness lifted : OTerm α) : Formula α :=
  ((InternalComputabilityDownward.domain comp context sigma tau f a ⊓
      InternalAccessibilityRules.certificate src false context f g witness) ⊓
    ((InternalComputabilityApplication.accepted comp sigma tau (numeral context) f a out ⊓
      InternalComputabilityApplication.accepted comp sigma tau (numeral context) g a other) ⊓
      programGraph lift lifted
        (InternalComputabilityDownward.liftArguments context sigma tau a witness)))

/-- Keep the ENTIRE existing antecedent on the left and add precisely one
literal fixed-Gamma argument graph on the right. No output/raw witness, target
typing, activation, old-typed, H-fixed or N-fixed assumption is added. -/
def fiberPremises {α : Type} (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (lift : Program 5) (context : Nat)
    (Gamma : List Ty) (sigma tau : Ty)
    (f g a out other witness lifted : OTerm α) : Formula α :=
  originalPremises src comp lift context sigma tau f g a out other witness lifted ⊓
    argumentFiber Gamma a

/-- This is NOT the existing unqualified CertifiedApplicationLift predicate.
It retains that predicate's source body, empty context, all term quantifiers,
exact original application/path graphs and full original output certificate. -/
def FiberCertifiedApplicationLift (src : SourcePresentation.Data)
    (comp : JointGammaComputability.Data) (lift : Program 5)
    (context : Nat) (Gamma : List Ty) : Prop :=
  ∀ (α : Type) (sigma tau : Ty) (f g a out other witness lifted : OTerm α),
  Nonempty (Derivation (SourcePresentation.sourceBody src context) []
    ((fiberPremises src comp lift context Gamma sigma tau
      f g a out other witness lifted).imp
      (InternalAccessibilityRules.certificate src false context out other lifted)))

/-- A stronger arithmetic helper on this SAME explicit package. Bodies and
ambient assumptions are arbitrary; the conclusion is the WHOLE assembled
source checker, including Gamma and typed-target/same-tag guards. -/
def LiftAtAnyBody (K : Nat) (Gamma : List Ty) (p : Selection) : Prop :=
  ∀ (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (f g a out other witness lifted : OTerm α),
  Nonempty (Derivation body Delta
    ((fiberPremises (src K Gamma p) (comp K Gamma p) (lift K Gamma p)
      K Gamma sigma tau f g a out other witness lifted).imp
      (InternalAccessibilityRules.certificate (src K Gamma p) false K out other lifted)))

def rawTyped {α : Type} (p : Selection) (tau : Ty) (x : OTerm α) : Formula α :=
  InternalCanonicalQuotientEdgeSelection.typedAccepted p.canonical x (numeral (typeNumber tau))

def rawPositive {α : Type} (p : Selection) (x y witness : OTerm α) : Formula α :=
  InternalPathChecker.positiveGraph
    (InternalCanonicalQuotientEdgeSelection.edgeChecker p.canonical) x y witness

/-- The input extraction conclusion. The original object right coordinates
are RAW and arbitrary. All three coordinate pairs, both function typings,
argument typing and the exact original raw certificate are derived internally. -/
def inputData {α : Type} (Gamma : List Ty) (p : Selection) (sigma tau : Ty)
    (f g a witness x y u : OTerm α) : Formula α :=
  InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma f x ⊓
    (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma g y ⊓
      (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma a u ⊓
        (rawTyped p (.arrow sigma tau) x ⊓
          (rawTyped p (.arrow sigma tau) y ⊓
            (rawTyped p sigma u ⊓ rawPositive p x y witness)))))

/-- The raw inputs are existential CONCLUSIONS, never new premises of the
certified lift. Original Program graph totality supplies these witnesses. -/
def inputDataExists {α : Type} (Gamma : List Ty) (p : Selection) (sigma tau : Ty)
    (f g a witness : OTerm α) : Formula α :=
  InternalFiniteBlocks.block (inputData Gamma p sigma tau
    (f.relabel Sum.inl) (g.relabel Sum.inl) (a.relabel Sum.inl) (witness.relabel Sum.inl)
    (.var (.inr (0 : Fin 3))) (.var (.inr 1)) (.var (.inr 2)))

/-- Both output coordinates and codomain typings accompany the transported
raw positive path. These are conclusions about the SUPPLIED original outputs
and supplied lift graph output, not replacement endpoints or certificates. -/
def transportedOutputs {α : Type} (Gamma : List Ty) (p : Selection) (tau : Ty)
    (out other lifted rawOut rawOther : OTerm α) : Formula α :=
  InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma out rawOut ⊓
    (InternalOriginalObjectFiberSourceDispatch.objectCoordinates Gamma other rawOther ⊓
      (rawTyped p tau rawOut ⊓
        (rawTyped p tau rawOther ⊓ rawPositive p rawOut rawOther lifted)))

def transportedOutputsExist {α : Type} (Gamma : List Ty) (p : Selection) (tau : Ty)
    (out other lifted : OTerm α) : Formula α :=
  InternalFiniteBlocks.block (transportedOutputs Gamma p tau
    (out.relabel Sum.inl) (other.relabel Sum.inl) (lifted.relabel Sum.inl)
    (.var (.inr (0 : Fin 2))) (.var (.inr 1)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalObjectFiberCertifiedLift
