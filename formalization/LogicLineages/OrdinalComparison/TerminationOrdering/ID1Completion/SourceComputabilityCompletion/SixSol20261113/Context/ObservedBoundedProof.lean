module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedPositionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedAllTestsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedBoundedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open InternalRecursionGraphStepSyntaxProof
open InternalParameterizedCanonicalResultFoldSyntaxProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open UniformCertificateCompletion ObservedClassDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem bounded (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) (out input typ parameter gamma count : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter)))
    (hg : Nonempty (Derivation body Delta (graph1 InternalUnpair.right gamma parameter)))
    (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph count gamma))) :
    Nonempty (Derivation body Delta (ObservedAllTestsDefinitions.BoundedTests
      (OriginalStructuralClassKeyDefinitions.key p H G W) count input out parameter)) := by
  unfold ObservedAllTestsDefinitions.BoundedTests
  apply actualFiniteUniversalIntroduction body alpha 1 Delta
  let j : alpha → alpha ⊕ Fin 1 := Sum.inl
  let cutoff : OTerm (alpha ⊕ Fin 1) := .var (.inr 0)
  let A := OriginalContextInsertion.Below cutoff (count.relabel j)
  let Theta := A :: Delta.map (fun q => q.relabel j)
  have inc : ∀ q ∈ Delta, q.relabel j ∈ Theta :=
    fun q hq => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨q,hq,rfl⟩)
  have ha' : Nonempty (Derivation body Theta
      (premises p H G W P (out.relabel j) (input.relabel j) (typ.relabel j) (parameter.relabel j))) := by
    simpa only [premises, conjunctionRename, OriginalFunctionNeutrality.windowGraph,
      OriginalVariableRepresentative.windowGraph, graph2Rename,
      InternalOriginalStepGuard.one, sucRelabel, zRelabel, sourcePremisesRename, foldGraphRename]
      using renameInto ha j Theta inc
  have hg' := renameInto hg j Theta inc
  rw [graph1Rename] at hg'
  have hl' := renameInto hl j Theta inc
  simp only [OriginalContextInsertion.lengthGraph,graph1Rename] at hl'
  have hc := unaryValue OriginalContextInsertion.length InternalUnpair.right
    (count.relabel j) (gamma.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0) hl' hg'
  have hb : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hr := OriginalIndexedObserverRangeSyntaxProof.rangeIntro cutoff (parameter.relabel j)
    (count.relabel j) (andIntro hc hb)
  obtain ⟨h⟩ := ObservedPositionProof.position p H G W P (out.relabel j) (input.relabel j)
    (typ.relabel j) (parameter.relabel j) cutoff ha' hr
  exact ⟨Derivation.implicationIntroduction h⟩

theorem allTests (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2)
    (P : Program 3) (out input typ parameter : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (premises p H G W P out input typ parameter))) :
    Nonempty (Derivation body Delta (graph3 (OriginalClassContextAllPositionObserver.allTests
      (OriginalStructuralClassKeyDefinitions.key p H G W)) (suc z) input out parameter)) := by
  apply programCases InternalUnpair.right (Fin.cons parameter Fin.elim0) _
  intro beta j Theta gamma hj hg
  apply programCases OriginalContextInsertion.length (Fin.cons gamma Fin.elim0) _
  intro beta' k Xi count hk hl
  simp only [graph3Rename,sucRelabel,zRelabel]
  have ha' : Nonempty (Derivation body Xi (premises p H G W P
      ((out.relabel j).relabel k) ((input.relabel j).relabel k)
      ((typ.relabel j).relabel k) ((parameter.relabel j).relabel k))) := by
    simpa only [premises, conjunctionRename, OriginalFunctionNeutrality.windowGraph,
      OriginalVariableRepresentative.windowGraph, graph2Rename,
      InternalOriginalStepGuard.one, sucRelabel, zRelabel, sourcePremisesRename, foldGraphRename]
      using renameInto (renameInto ha j Theta hj) k Xi hk
  have hg' := renameInto hg k Xi hk
  simp only [programRename,consTermRename,emptyRename] at hg'
  simp only [consTermRename,emptyRename] at hl
  exact ObservedAllTestsProof.actualAllTests (OriginalStructuralClassKeyDefinitions.key p H G W)
    body beta' Xi ((input.relabel j).relabel k) ((out.relabel j).relabel k)
    ((parameter.relabel j).relabel k) (gamma.relabel k) count hg' hl
    (bounded p H G W P _ _ _ _ _ _ ha' hg' hl)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedBoundedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ObservedBoundedProof
