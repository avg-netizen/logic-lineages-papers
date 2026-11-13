module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Integration.CorrectedFinalErasureTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Literal witnesses [Gamma,x,y,parameter,entry,tail,vertex,quotient,s,t,k].
The raw W, both folds and the suffix path use ONE unchanged final tuple and
ONE original runtime parameter. These fields change no source relation. -/
def Fields {alpha : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) (ys : Fin 11 → OTerm alpha) : Formula alpha :=
  let D := OuterSelection.data q.base q.window
  let Objects := graph2 InternalPairing.pairing f (ys 0) (ys 1) ⊓
    (graph2 InternalPairing.pairing g (ys 0) (ys 2) ⊓
      graph2 InternalPairing.pairing (ys 3) (numeral context) (ys 0))
  let Codes := graph2 InternalListCodec.consCode path (ys 4) (ys 5) ⊓
    (graph2 InternalPairing.pairing (ys 4) (ys 6) (ys 7) ⊓
      (graph3 edgeCode (ys 7) (ys 8) (ys 9) (ys 10) ⊓
        selectors (ys 7) (ys 8) (ys 9) (ys 10)))
  let Raw := stepAccepted D q.oldStep (ys 8) (ys 9) (ys 10) (ys 3) ⊓
    (InternalParameterizedCanonicalResultFold.foldGraph D (ys 1) (ys 8) (ys 3) ⊓
      InternalParameterizedCanonicalResultFold.foldGraph D (ys 6) (ys 9) (ys 3))
  let Suffix := InternalParameterizedPathChecker.pathGraph (edgeChecker D q.oldStep)
    (ys 6) (ys 2) (ys 5) (ys 3)
  Objects ⊓ (Codes ⊓ (Raw ⊓ Suffix))

def Matrix {alpha : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) : Formula (alpha ⊕ Fin 11) :=
  Fields q context (f.relabel Sum.inl) (g.relabel Sum.inl) (path.relabel Sum.inl)
    (fun i => .var (.inr i))

def Witness {alpha : Type} (q : GlobalSourcePackage.Inputs) (context : Nat)
    (f g path : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (Matrix q context f g path)

/-- Expose the first ACTUAL raw step of an arbitrary ORIGINAL positive
certificate at the retained final tuple. Nonemptiness, all constructor and
selector witnesses, SAME-Gamma, both final fold graphs and the literal
reflexive suffix are derived internally. No recognition, decomposition,
canonical fixedness, root semantics or source-edge transformer is supplied. -/
def ActualOriginalPositiveFirstRawStep : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (context : Nat) (f g path : OTerm alpha),
  let q := Integration.preparedKernelFinalInputs p H G W P
  Nonempty (Derivation body Delta
    ((graph1 q.window (numeral 1) (numeral context) ⊓
      InternalAccessibilityRules.certificate (GlobalSourcePackage.source q) false context f g path).imp
      (Witness q context f g path)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.PositiveSourceExposureTargets
