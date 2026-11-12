module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepWrapperTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (existsOne)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def Certificate {alpha : Type} (leaf : Program 4) (s t parameter cert : OTerm alpha) : Formula alpha :=
  graph4 leaf InternalOriginalStepGuard.one s t cert parameter

def WitnessMatrix {alpha : Type} (leaf : Program 4) (s t parameter : OTerm alpha) : Formula (alpha ⊕ Fin 1) :=
  Certificate leaf (s.relabel Sum.inl) (t.relabel Sum.inl) (parameter.relabel Sum.inl) (.var (.inr 0))

def Witness {alpha : Type} (leaf : Program 4) (s t parameter : OTerm alpha) : Formula alpha :=
  existsOne (WitnessMatrix leaf s t parameter)

def Result {alpha : Type} (leaf : Program 4) (s t parameter : OTerm alpha) : Formula alpha :=
  equal s t ⊔ Witness leaf s t parameter

/-- This frame is at the transformed parameter and SAME actual leaf. Source
validity is consumed from the existing transport theorem, never inferred by
native calibration. The certificate prefix is constructed later. -/
def Frame {alpha : Type} (source : Program 2)
    (s t parameter childS childT childParam d e context gamma extended : OTerm alpha) : Formula alpha :=
  graph2 source InternalOriginalStepGuard.one s parameter ⊓
    (graph3 OriginalLambdaConstructor.constructor s d e childS ⊓
      (graph3 OriginalLambdaConstructor.constructor t d e childT ⊓
        (graph1 InternalUnpair.left e childS ⊓
          (graph1 InternalUnpair.left e childT ⊓
            (graph2 InternalPairing.pairing parameter context gamma ⊓
              (graph2 InternalListCodec.consCode extended d gamma ⊓
                graph2 InternalPairing.pairing childParam context extended))))))

/-- Explicit induction supplier in continuation form, stable under the fresh
certificate binder. This is NOT asserted to exist: a full erasure induction
must prove and instantiate it for the original child certificate. -/
def ChildSupplier {alpha : Type} (leaf : Program 4) (body : Positive (Fin 1))
    (Delta : List (Formula alpha)) (childS childT childParam : OTerm alpha) : Prop :=
  ∀ psi : Formula alpha,
  (Nonempty (Derivation body Delta (equal childS childT)) → Nonempty (Derivation body Delta psi)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (cert : OTerm beta),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    Nonempty (Derivation body Theta
      (Certificate leaf (childS.relabel j) (childT.relabel j) (childParam.relabel j) cert)) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

/-- Supporting λ case only, conditional on an explicit child induction
supplier. No full certificate transport, quotient equality, or rank theorem. -/
def LocalCongruence : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter childS childT childParam d e context gamma extended : OTerm alpha),
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined source oldStep)
  Nonempty (Derivation body Delta (Frame source s t parameter childS childT childParam d e context gamma extended)) →
  ChildSupplier leaf body Delta childS childT childParam →
  Nonempty (Derivation body Delta (Result leaf s t parameter))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyDefinitions
