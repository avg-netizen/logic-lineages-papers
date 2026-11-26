module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaValidityInternalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinal
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open OriginalTransparentLambdaValidityInternal (TagIs BooleanOutput LambdaShape SourceLambdaRootFactors)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The ACTUAL original final selection, with an arbitrary representative
replacement before it. Only oldRepresentative is freely replaced here; HS,
HT and the original member remain those of the SAME raw Data. The unchanged
OuterSelection performs bottom normalization and member normalization once.
No calibration, canonical traversal, or representative invariant is required. -/
def selectedData (rawData : Data) (representative : Program 2)
    (window : Program 1) : Data :=
  OuterSelection.data
    { OriginalTransparentLambdaValidity.refineData rawData with
      oldRepresentative := representative } window

/-- Exact all-output collapse of the ACTUAL application-only target fold.
This is an internal arithmetic law, not numerical equality or a replacement
target relation. The raw input and parameter are wholly arbitrary. -/
def TargetCollapse (rawData selected : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (InternalOriginalUniformDescentSelection.targetValidity selected)
        out raw parameter).iff
      (graph2 (OriginalTransparentLambdaValidity.targetValidator rawData)
        out raw parameter)))

/-- The actual original source-universe result fold collapses to HS on
ALL outputs. Its node callback is exactly selected.member, and its leaf is
exactly selected.oldSource, including the existing bottom normalization. -/
def UniverseCollapse (rawData selected : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (InternalParameterizedApplicationValidityFold.universeP
        selected.oldSource selected.member) out raw parameter).iff
      (graph2 (OriginalTransparentLambdaValidity.sourceValidator rawData)
        out raw parameter)))

/-- Retain BOTH literal conjuncts of the actual final source. No additional
HS-implies-HT supplier is needed or silently assumed. This graph equation
does not replace the source used by the original global package. -/
def SourceCollapse (rawData selected : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (InternalOriginalUniformDescentSelection.validity selected)
        out raw parameter).iff
      (graph2 (InternalAcceptance.conjunction
        (OriginalTransparentLambdaValidity.targetValidator rawData)
        (OriginalTransparentLambdaValidity.sourceValidator rawData))
        out raw parameter)))

def CollapseLaws (rawData selected : Data) : Prop :=
  TargetCollapse rawData selected ∧ UniverseCollapse rawData selected ∧
    SourceCollapse rawData selected

/-- This is literally the original RootLambdaChild witness block with ONLY
its validator call changed to the supplied ACTUAL final Program. The original
initial state, currentBody, ExtendedParameter and childParameter graphs are
retained, so the body is the actual repacked body at the actual single cons
extension of encoded Gamma and the SAME outer context. The witnesses are
internal; no body validity or successful extension is supplied externally. -/
def FinalLambdaChild {alpha : Type} (valid : Program 2)
    (raw parameter : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 3)
    (graph2 initial (.var (.inr (0 : Fin 3)))
        (raw.relabel Sum.inl) (parameter.relabel Sum.inl) ⊓
      (graph1 currentBody (.var (.inr (1 : Fin 3))) (.var (.inr (0 : Fin 3))) ⊓
        (ExtendedParameter (raw.relabel Sum.inl) (parameter.relabel Sum.inl)
            (.var (.inr (2 : Fin 3)))) ⊓
          (graph1 childParameter (.var (.inr (2 : Fin 3))) (.var (.inr (0 : Fin 3))) ⊓
            graph2 valid (numeral 1)
              (.var (.inr (1 : Fin 3))) (.var (.inr (2 : Fin 3))))))

/-- BOTH outer-arrow and payload-domain memberships use the SAME actual
selected.member. The actual body's validity is a conclusion factor at the
IDENTICAL final source Program, not HS or an earlier selected Data. -/
def FinalSourceLambdaFactors {alpha : Type} (selected : Data)
    (raw parameter : OTerm alpha) : Formula alpha :=
  SourceLambdaRootFactors selected raw parameter ⊓
    FinalLambdaChild (InternalOriginalUniformDescentSelection.validity selected)
      raw parameter

/-- Target lambda factors contain NO source-window membership or source
acceptance. Its actual body calls the SAME actual final target Program. -/
def FinalTargetLambdaFactors {alpha : Type} (selected : Data)
    (raw parameter : OTerm alpha) : Formula alpha :=
  LambdaShape raw ⊓
    FinalLambdaChild (InternalOriginalUniformDescentSelection.targetValidity selected)
      raw parameter

/-- Full-output elimination AND reconstruction of final source lambdas.
The sole shape premise is the literal lambda tag. All actual arrow/domain
shape, membership and final body acceptance tests are on the factor side
of the equivalence; rejection is characterized as well as acceptance. -/
def SourceLambdaLaw (selected : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((TagIs 1 raw).imp
      ((graph2 (InternalOriginalUniformDescentSelection.validity selected)
          out raw parameter).iff
        (BooleanOutput out (FinalSourceLambdaFactors selected raw parameter)))))

/-- Full-output elimination AND reconstruction at the final target Program.
No source membership, supplied body validity, native calibration, replacement
relation or earlier-Data shortcut occurs in the internal statement. -/
def TargetLambdaLaw (selected : Data) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (out raw parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((TagIs 1 raw).imp
      ((graph2 (InternalOriginalUniformDescentSelection.targetValidity selected)
          out raw parameter).iff
        (BooleanOutput out (FinalTargetLambdaFactors selected raw parameter)))))

def InternalLaws (rawData selected : Data) : Prop :=
  CollapseLaws rawData selected ∧ SourceLambdaLaw selected ∧ TargetLambdaLaw selected

/-- Refine the original globally selected validity leaves ONCE, before all
windows and runtime Gamma. All remaining original input fields are literal. -/
def refineInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  { p with base := OriginalTransparentLambdaValidity.refineData p.base }

/-- The complete already accepted final pipeline is retained unchanged. -/
def finalInputs (p : GlobalSourcePackage.Inputs) : GlobalSourcePackage.Inputs :=
  OriginalHereditaryLambdaGlobal.finalInputs (refineInputs p)

/-- The ACTUAL shared Data used by source, computability, quotient edges,
actualJ and path consumers of that SAME final input tuple. -/
def finalData (p : GlobalSourcePackage.Inputs) : Data :=
  OuterSelection.data (finalInputs p).base (finalInputs p).window

/-- Native refinement is separate from the independent internal laws.
The complete original input calibration survives, with all four base leaves
equal on every raw vector, including malformed and rejected inputs. -/
def NativeRefinement (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  GlobalSourcePackage.InputsCalibrated n arity (refineInputs p) ∧
    (∀ v : List.Vector Nat 2,
      evaluate (refineInputs p).base.oldSource v = evaluate p.base.oldSource v ∧
      evaluate (refineInputs p).base.oldTarget v = evaluate p.base.oldTarget v ∧
      evaluate (refineInputs p).base.oldRepresentative v = evaluate p.base.oldRepresentative v ∧
      evaluate (refineInputs p).base.member v = evaluate p.base.member v)

/-- Retain the ENTIRE preceding Properties conjunction literally, including
the full original Package, all final calibration and every prior certificate,
neutral, variable and hereditary-leaf consumer. The new internal laws refer
to precisely that same final tuple. This packet does not assert canonical
body coherence, weakening/substitution, lambda computability or closed ID1. -/
def Properties (n : Nat) (arity : Fin n → Nat)
    (p : GlobalSourcePackage.Inputs) : Prop :=
  NativeRefinement n arity p ∧
    OriginalHereditaryLambdaGlobal.Properties n arity (refineInputs p) ∧
      InternalLaws p.base (finalData p)

/- FROZEN NEXT-BRIDGE SPECIFICATION, NOT AN ACCEPTANCE CLAIM.

1. Prove literal selected-field identities. Use independent internal exact-
   bottom normalization to remove only the normalization of HS and HT.
2. Use the actual application-only result fold's internal application/leaf
   equations, the framed validator's independent internal app recurrence,
   and strong induction on ORIGINAL payload to prove target/universe collapse.
   Conjunction graph laws then yield the full final source equation.
3. Combine the independent local lambda full-output equations with collapse
   at the SAME actual body and extended parameter. Fuse the original witness
   blocks using graph functionality, retaining every original selector.
4. Use native refinement ONLY to apply the existing global Properties
   theorem at refineInputs p. Instantiate the independent generic laws via
   the literal finalData identity. No native equality reflects into a graph.

All internal laws are unconditional in rawData, representative and window.
The arbitrary representative parameter permits later canonical refinements
without assuming those refinements or changing these validity contracts. -/

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaFinal
