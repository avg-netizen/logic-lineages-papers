module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDichotomyDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Strict rank decrease between ORIGINAL packed endpoints. The two supplied
ranks are actual all-variable-occurrence graphs, not maximum indices, free
variable counts, transformed ranks or canonical Object ranks. -/
def PackedRankDrop {alpha : Type} (oldS oldT before after : OTerm alpha) : Formula alpha :=
  graph1 OriginalRawSyntaxTransport.variableRankPackedRaw before oldS ⊓
    (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw after oldT ⊓
      InternalLessThan.strictLess after before)

def ConstructorLift : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (oldS oldT oldChildS oldChildT d e before after : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph3 OriginalLambdaConstructor.constructor oldS d e oldChildS ⊓
      (graph3 OriginalLambdaConstructor.constructor oldT d e oldChildT ⊓
        PackedRankDrop oldChildS oldChildT before after)).imp
      (PackedRankDrop oldS oldT before after)))

/-- Equality concerns transformed endpoints; strict decrease concerns only
original endpoints. The certificate alternative uses the SAME effective leaf. -/
def Result {alpha : Type} (leaf : Program 4)
    (s t parameter oldS oldT before after : OTerm alpha) : Formula alpha :=
  (equal s t ⊓ PackedRankDrop oldS oldT before after) ⊔
    OriginalLambdaErasureSquareDichotomyDefinitions.Witness leaf s t parameter

def ChildSupplier {alpha : Type} (leaf : Program 4) (body : Positive (Fin 1))
    (Delta : List (Formula alpha))
    (childS childT childParam oldChildS oldChildT before after : OTerm alpha) : Prop :=
  ∀ psi : Formula alpha,
  (Nonempty (Derivation body Delta
    (equal childS childT ⊓ PackedRankDrop oldChildS oldChildT before after)) →
      Nonempty (Derivation body Delta psi)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (cert : OTerm beta),
    (∀ h ∈ Delta, h.relabel j ∈ Theta) →
    Nonempty (Derivation body Theta
      (OriginalLambdaErasureSquareDichotomyDefinitions.Certificate leaf
        (childS.relabel j) (childT.relabel j) (childParam.relabel j) cert)) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)

/-- Local induction closure only. The supplier is a required explicit IH,
not a new axiom, native reflection or an assertion of global erasure. -/
def LocalRankedCongruence : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter childS childT childParam d e context gamma extended
      oldS oldT oldChildS oldChildT before after : OTerm alpha),
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined source oldStep)
  Nonempty (Derivation body Delta
    (OriginalLambdaErasureSquareDichotomyDefinitions.Frame source
      s t parameter childS childT childParam d e context gamma extended)) →
  Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldS d e oldChildS)) →
  Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldT d e oldChildT)) →
  ChildSupplier leaf body Delta childS childT childParam oldChildS oldChildT before after →
  Nonempty (Derivation body Delta (Result leaf s t parameter oldS oldT before after))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
