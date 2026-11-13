module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.CorrectedTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedDirectBottomTraceFrontQueryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.RootSoundnessProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalTagArithmeticSyntaxProof (z suc eqn zRelabel sucRelabel)
open OriginalHereditaryLambdaChildStateProof (atLiveRecover)
open OriginalMixedDirectBottomTrace
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Each actual selected hop checks the ORIGINAL source and SAME root leaf.
The source is recovered from its runtime projections, not assumed from the
child's source validity. -/
theorem hopRoot (source : Program 2) (leaf rest : Program 4)
 (s t cert parameter state : OTerm alpha)
 (hl : Nonempty (Derivation body Delta
  (graph4 OriginalHereditaryLambda.live state s t cert parameter)))
 (hh : Nonempty (Derivation body Delta
  (graph1 (OriginalHereditaryLambda.atState
   (InternalAcceptance.conjunction
    (InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source) rest) leaf))
   (suc z) state))) :
 Nonempty (Derivation body Delta
  (graph2 source (suc z) s parameter ⊓ graph4 leaf (suc z) s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := ![s,t,cert,parameter]
 have h := atLiveRecover (InternalAcceptance.conjunction
  (InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source) rest) leaf)
  (suc z) state s t cert parameter hl hh
 have hp := conjunctionRecover
  (InternalAcceptance.conjunction (OriginalTransparentVariableStep.sourceAt source) rest) leaf xs h
 have hs := conjunctionRecover (OriginalTransparentVariableStep.sourceAt source) rest xs (andLeft hp)
 exact andIntro
  (binaryRecover source (.projection 0) (.projection 3) (suc z) s parameter xs
   (andLeft hs) (projectionValue 0 xs) (projectionValue 3 xs))
  (andRight hp)

/-- An accepted nonempty trace pays its original root edge in either
actual branch. Existing front descent proves that one branch succeeded. -/
theorem atCons (source : Program 2) (leaf : Program 4)
 (s t cert parameter path head tail : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left path cert)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode path head tail)))
 (ha : Nonempty (Derivation body Delta
  (graph4 (recognizes source leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph2 source (suc z) s parameter ⊓ graph4 leaf (suc z) s t cert parameter)) := by
 apply OriginalMixedDirectBottomTraceFrontQueryProof.frontCases source leaf
  s t cert parameter path head tail _ hp hc ha
 intro beta rho Theta state next out hrho hl hb hr hf
 simp only [conjunctionRename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
 let A := graph1 (OriginalHereditaryLambda.atState (lambdaHop source leaf)) (suc z) state ⊓
  graph1 (OriginalHereditaryLambda.atState OriginalHereditaryLambda.childLive) next state
 let B := graph1 (OriginalHereditaryLambda.atState (applicationHop source leaf)) (suc z) state ⊓
  graph1 (OriginalHereditaryLambda.atState OriginalTransparentApplicationFunctionDefinitions.childLive) next state
 have hA : Nonempty (Derivation body (A :: Theta)
  (graph2 source (suc z) (s.relabel rho) (parameter.relabel rho) ⊓
   graph4 leaf (suc z) (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho))) := by
  have h : Nonempty (Derivation body (A :: Theta) A) :=
   ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact hopRoot source leaf
   (InternalAcceptance.conjunction OriginalLambdaGuardLeaf.sourceLambda
    (InternalAcceptance.conjunction OriginalLambdaGuardLeaf.matchingTarget OriginalHereditaryLambda.lamPath))
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho) state
   (withHyp hl A) (andLeft h)
 have hB : Nonempty (Derivation body (B :: Theta)
  (graph2 source (suc z) (s.relabel rho) (parameter.relabel rho) ⊓
   graph4 leaf (suc z) (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho))) := by
  have h : Nonempty (Derivation body (B :: Theta) B) :=
   ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact hopRoot source leaf OriginalTransparentApplicationFunctionDefinitions.structuralGuard
   (s.relabel rho) (t.relabel rho) (cert.relabel rho) (parameter.relabel rho) state
   (withHyp hl B) (andLeft h)
 obtain ⟨hA⟩ := hA
 obtain ⟨hB⟩ := hB
 obtain ⟨hb⟩ := hb
 exact ⟨InternalBetaTotalityProof.disjunctionElimination hb
  (Derivation.implicationIntroduction hA) (Derivation.implicationIntroduction hB)⟩

/-- Only nil/cons decomposition of the actual original certificate path is
needed: the terminal or first successful hop already checks the root. -/
theorem atPath (source : Program 2) (leaf : Program 4)
 (s t cert parameter path : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left path cert)))
 (ha : Nonempty (Derivation body Delta
  (graph4 (recognizes source leaf) (suc z) s t cert parameter))) :
 Nonempty (Derivation body Delta
  (graph2 source (suc z) s parameter ⊓ graph4 leaf (suc z) s t cert parameter)) := by
 apply OriginalContextInsertionLengthProof.listCases path _
 · have he : Nonempty (Derivation body ((eqn path z) :: Delta) (eqn path z)) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
   have hz := outputTransport InternalUnpair.left path z (Fin.cons cert Fin.elim0)
    he (withHyp hp (eqn path z))
   have ht := OriginalMixedDirectBottomTraceBaseProof.actualNilBase source leaf body alpha
    ((eqn path z) :: Delta) s t cert parameter hz (withHyp ha (eqn path z))
   exact andIntro (andLeft ht) (andLeft (andRight ht))
 · intro beta rho Theta head tail hrho hc
   simp only [conjunctionRename,graph2Rename,graph4Rename,sucRelabel,zRelabel]
   have hp' := renameInto hp rho Theta hrho
   have ha' := renameInto ha rho Theta hrho
   simp only [graph1Rename] at hp'
   simp only [graph4Rename,sucRelabel,zRelabel] at ha'
   exact atCons source leaf (s.relabel rho) (t.relabel rho) (cert.relabel rho)
    (parameter.relabel rho) (path.relabel rho) head tail hp' hc ha'

theorem recognizerRootSoundness : CorrectedTargets.RecognizerRootSoundness := by
 intro source leaf body alpha Delta s t cert parameter ha
 apply programCases InternalUnpair.left (Fin.cons cert Fin.elim0) _
 intro beta rho Theta path hrho hp
 simp only [conjunctionRename,graph2Rename,graph4Rename,
  GuardedSourceSyntaxProof.numeralRename]
 simp only [consTermRename,emptyRename] at hp
 have ha' := renameInto ha rho Theta hrho
 simp only [graph4Rename,GuardedSourceSyntaxProof.numeralRename] at ha'
 exact atPath source leaf (s.relabel rho) (t.relabel rho) (cert.relabel rho)
  (parameter.relabel rho) path hp ha'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.RootSoundnessProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Erasure.RootSoundnessProof
