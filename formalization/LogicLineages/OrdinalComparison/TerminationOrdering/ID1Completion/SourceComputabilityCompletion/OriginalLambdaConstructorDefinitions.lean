module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructor
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ORIGINAL typeNumber (.arrow sigma tau) constructor, successor of pair.
This is a type NUMBER, not an Encodable Ty or Gamma code. -/
def arrow : Program 2 := InternalListCodec.consCode

/-- Inputs [domain type number,codomain type number,body payload].
Literal packedNumber/codeNumber lambda equation from
NumberedLeastCodeRepresentativeDefinitions; no replacement term encoding. -/
def packedLambda : Program 3 :=
  pairOf (consOf (.projection 0) (.projection 1))
    (pairOf (InternalLessThan.constantOne 3)
      (pairOf (.projection 0) (.projection 2)))

/-- Inputs [domain,codomain,packed body]. Only the original outer body type
field is discarded. Off-domain behavior is this explicit total AST. -/
def constructor : Program 3 :=
  .composition packedLambda
    ![.projection 0,.projection 1,rightOf (.projection 2)]

def tag : Program 1 := leftOf (rightOf (.projection 0))
def domain : Program 1 := leftOf (rightOf (rightOf (.projection 0)))
def bodyPayload : Program 1 := rightOf (rightOf (rightOf (.projection 0)))

/-- Inputs [codomain,packed lambda]. Repack the actual body payload with the
supplied original codomain number. No canonicalization is performed. -/
def bodyCode : Program 2 :=
  pairOf (.projection 0)
    (.composition bodyPayload (fun _ : Fin 1 => .projection 1))

/-- Explicit field witnesses for the literal raw lambda. The supplied outer
arrow number and packed body are shared by all conjuncts. -/
def Fields {alpha : Type} (out d e b arrowCode : OTerm alpha) : Formula alpha :=
  graph1 tag (SourceComputabilityFormulaSupportProof.numeral 1) out ⊓
    (graph1 InternalUnpair.left arrowCode out ⊓
      (graph2 arrow arrowCode d e ⊓
        (graph1 domain d out ⊓ graph2 bodyCode b e out)))

/-- Raw constructor algebra only. In a typed source application b belongs to
sigma::Gamma and out belongs to Gamma. These definitions do NOT identify
ContextUniform.Object's Encodable Gamma with typesNumber Gamma, and do not
assert domain membership, computability, normalization or lambda-step laws. -/
def ConstructorFields : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out d e b arrowCode : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((graph3 constructor out d e b ⊓
      (graph1 InternalUnpair.left e b ⊓ graph2 arrow arrowCode d e)).imp
        (Fields out d e b arrowCode)))

def ConstructorReconstruction : Prop :=
  ∀ (positive : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out d e b arrowCode : OTerm alpha),
  Nonempty (Derivation positive Delta
    ((Fields out d e b arrowCode).imp (graph3 constructor out d e b)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructor
