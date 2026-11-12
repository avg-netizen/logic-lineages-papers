module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextExtensionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObject
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Every unary selector receives the ORIGINAL Object in input slot 0.
Its right coordinate is the original raw packed term, and its left coordinate
is the original Encodable Gamma code. No decoding or canonicalization is
inserted into these total Programs. -/
def lambdaTag : Program 1 :=
  .composition OriginalLambdaConstructor.tag (fun _ : Fin 1 => InternalUnpair.right)

def domainCode : Program 1 :=
  .composition OriginalLambdaConstructor.domain (fun _ : Fin 1 => InternalUnpair.right)

def codomainCode : Program 1 :=
  .composition OriginalLambdaTraversal.rawCodomain (fun _ : Fin 1 => InternalUnpair.right)

def packedBody : Program 1 :=
  .composition OriginalLambdaTraversal.rawBody (fun _ : Fin 1 => InternalUnpair.right)

/-- Extract the actual original lambda body Object: cons the actual payload
domain onto Encodable Gamma and retain the actual repacked body. This total
AST does not itself assert that its input is a well-typed lambda. -/
def bodyObject : Program 1 :=
  pairOf (consOf domainCode InternalUnpair.left) packedBody

/-- The same single initial guard, transparent selection and single variable
refinement used by the accepted final-rank and canonical Object contracts. -/
abbrev refined := OriginalFinalGuardedRank.refined

def finalInputs (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalLambdaTraversalSelection.finalInputs (refined p H G W)

def finalData (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) :=
  OriginalLambdaTraversalSelection.finalData (refined p H G W)

/-- Original outer-window acceptance, original input typing and the literal
lambda tag are the complete semantic input conditions. Requested type, input
Object and runtime context remain the caller's original values. -/
def Premise (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    {alpha : Type} (context : Nat) (typ input : OTerm alpha) : Formula alpha :=
  let f := finalInputs p H G W
  graph1 f.window (numeral 1) (numeral context) ⊓
    (graph3 (GlobalSourcePackage.computability f).typed
        (numeral 1) (numeral context) typ input ⊓
      graph1 lambdaTag (numeral 1) input)

/-- All coordinates belong to the supplied parent and its actual extracted
body. The context extension uses literal cons at the SAME outer context;
Fields and constructor retain the original packed lambda relation. The
selected typed factors explicitly include body membership, source validity,
outer codomain and transition fixedness at the SAME final Data. They are
conclusions, as are actual selected typing and original outer Object typing.
No body fixedness, child membership, native context or native evaluation is
an input to the exposure contract below. -/
def Recovered (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    {alpha : Type} (context : Nat)
    (typ input gamma raw d e bodyRaw parameter extended bodyParameter childObject : OTerm alpha) :
    Formula alpha :=
  let D := finalData p H G W
  let f := finalInputs p H G W
  OriginalContextExtension.Recovered (numeral context) d input bodyRaw
      gamma raw parameter extended bodyParameter childObject ⊓
    (OriginalLambdaConstructor.Fields raw d e bodyRaw typ ⊓
      (graph3 OriginalLambdaConstructor.constructor raw d e bodyRaw ⊓
        (OriginalLambdaTraversalInternal.LambdaFields raw d e bodyRaw parameter bodyParameter ⊓
          (graph1 codomainCode e input ⊓
            (graph1 bodyObject childObject input ⊓
              (InternalOriginalUniformDescentSelection.typedFactors
                  D.oldRepresentative (InternalOriginalUniformDescentSelection.validity D)
                  D.member bodyRaw e bodyParameter ⊓
                (graph3 (InternalOriginalUniformDescentSelection.selectedTyped D)
                    (numeral 1) bodyRaw e bodyParameter ⊓
                  graph3 (GlobalSourcePackage.computability f).typed
                    (numeral 1) (numeral context) e childObject)))))))

/-- Bind every actual parent/body coordinate internally using original
Program totality. The continuation receives the literal context extension,
constructor relation and fully typed body at the unchanged final tuple.
The ambient variable injection and formula-context inclusion are explicit;
no free witness, source-oracle or prior body-typing premise is supplied. -/
def ExposureLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (typ input : OTerm alpha) (psi : Formula alpha),
  Nonempty (Derivation positive Delta (Premise p H G W context typ input)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    ∀ gamma raw d e bodyRaw parameter extended bodyParameter childObject : OTerm beta,
    Nonempty (Derivation positive Theta
      (Recovered p H G W context (typ.relabel j) (input.relabel j)
        gamma raw d e bodyRaw parameter extended bodyParameter childObject)) →
    Nonempty (Derivation positive Theta (psi.relabel j))) →
  Nonempty (Derivation positive Delta psi)

/-- Every actual output of the original body Object extractor is typed at
the actual selected codomain, under the SAME outer typed dispatch. Only the
input lambda is assumed typed; neither child canonicality nor child source
acceptance is an external premise. -/
def TypedLaw (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) : Prop :=
  let f := finalInputs p H G W
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (typ input e childObject : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((Premise p H G W context typ input ⊓
      (graph1 codomainCode e input ⊓ graph1 bodyObject childObject input)).imp
      (graph3 (GlobalSourcePackage.computability f).typed
        (numeral 1) (numeral context) e childObject)))

/- These contracts expose original internal body typing only. They do not
assert a lambda source-edge/certificate rule, computability of the body or
lambda, class coherence, canonical cancellation, substitution/I/C or the
closed all-term accessibility derivation. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaBodyObject
