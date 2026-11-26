module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSpineNonBottomProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalQuotientSpineRawProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedPathCheckerProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalSourceNeutralApplicationSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateGuardProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (unaryRecover)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Gamma : List (Formula alpha)}

def queries : Fin 4 → Program 2 :=
  let sm : Program 2 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 0)
  let tm : Program 2 := .composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 1)
  Fin.cons sm (Fin.cons tm
    (Fin.cons (.composition InternalUnpair.right (fun _ : Fin 1 => sm))
      (Fin.cons (.composition InternalUnpair.right (fun _ : Fin 1 => tm)) Fin.elim0)))

/-- Change only the path certificate coordinate of the literal endpoint
spine guard, and insert its independently derived non-bottom and positive
path factors. All observer values are bound by internal Program totality. -/
theorem positiveFromGuard (edge : Program 4) (x y child pathCode parameter : OTerm alpha)
    (hg : Nonempty (Derivation body Gamma
      (OriginalSpineGuardLeaf.spineAccepted x y child parameter)))
    (hp : Nonempty (Derivation body Gamma
      (InternalParameterizedPathChecker.positiveGraph edge x y pathCode parameter))) :
    Nonempty (Derivation body Gamma
      (PositiveGuard.accepted BottomRepresentative.bottomTest BottomSpineMeasure.measure
        edge x y pathCode parameter)) := by
  obtain ⟨hnb⟩ := OriginalSpineNonBottomProof.actualOriginalSpineGuardRejectsBottom
    body alpha Gamma x y child parameter
  obtain ⟨hguard⟩ := hg
  have hn : Nonempty (Derivation body Gamma
      (graph1 BottomRepresentative.bottomTest (suc z) x).not) :=
    ⟨Derivation.implicationElimination hnb hguard⟩
  let xs : Fin 2 → OTerm alpha := Fin.cons x (Fin.cons y Fin.elim0)
  apply queryCases queries xs _
  intro beta j ys Delta hj hq
  simp only [PositiveGuard.accepted,graph4Rename,InternalOriginalStepGuard.one,sucRelabel,zRelabel]
  let zs : Fin 2 → OTerm beta := fun i => (xs i).relabel j
  have hg' := renameInto ⟨hguard⟩ j Delta hj
  rw [OriginalQuotientSpineRawProof.spineRename] at hg'
  have hn' := renameInto hn j Delta hj
  simp only [OriginalSourceNeutralApplicationSyntaxProof.negationRename,graph1Rename,sucRelabel,zRelabel] at hn'
  have hp' := renameInto hp j Delta hj
  simp only [InternalParameterizedPathChecker.positiveGraph,
    InternalParameterizedPathChecker.checkerGraph,programRename,
    InternalParameterizedPathChecker.quadruple,consTermRename,emptyRename,
    sucRelabel,zRelabel] at hp'
  have hmS : Nonempty (Derivation body Delta
      (BottomSpineMeasure.graph (ys 0) (x.relabel j))) :=
    unaryRecover BottomSpineMeasure.measure (.projection 0) (ys 0) (x.relabel j) zs
      (hq 0) (projectionValue 0 zs)
  have hmT : Nonempty (Derivation body Delta
      (BottomSpineMeasure.graph (ys 1) (y.relabel j))) :=
    unaryRecover BottomSpineMeasure.measure (.projection 1) (ys 1) (y.relabel j) zs
      (hq 1) (projectionValue 1 zs)
  have hdS : Nonempty (Derivation body Delta (graph1 InternalUnpair.right (ys 2) (ys 0))) :=
    unaryRecover InternalUnpair.right (queries 0) (ys 2) (ys 0) zs (hq 2) (hq 0)
  have hdT : Nonempty (Derivation body Delta (graph1 InternalUnpair.right (ys 3) (ys 1))) :=
    unaryRecover InternalUnpair.right (queries 1) (ys 3) (ys 1) zs (hq 3) (hq 1)
  let rawInputs : Fin 4 → OTerm beta := Fin.cons (x.relabel j) (Fin.cons (y.relabel j)
    (Fin.cons (child.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)))
  have hc := PositiveSpineRulesProof.spineRecover BottomSpineMeasure.measure
    (ys 0) (ys 1) (ys 2) (ys 3) rawInputs hmS hmT hdS hdT hg'
  exact PositiveSpineRulesProof.value BottomRepresentative.bottomTest BottomSpineMeasure.measure
    edge (x.relabel j) (y.relabel j) (pathCode.relabel j) (parameter.relabel j)
    (ys 0) (ys 1) (ys 2) (ys 3)
    (andIntro hmS (andIntro hmT (andIntro hdS hdT)))
    (andIntro hp' (andIntro hn' hc))

/-- The original child certificate is the singleton entry's certificate;
the resulting source witness is the internally constructed original list. -/
theorem singletonPositive (data : InternalOriginalUniformDescentSelection.Data) (oldStep : Program 4)
    (x y child entry pathCode parameter : OTerm alpha)
    (he : Nonempty (Derivation body Gamma (edgeAccepted data oldStep x y child parameter)))
    (hp : Nonempty (Derivation body Gamma (graph2 InternalPairing.pairing entry y child)))
    (hc : Nonempty (Derivation body Gamma (graph2 InternalListCodec.consCode pathCode entry z))) :
    Nonempty (Derivation body Gamma
      (InternalParameterizedPathChecker.positiveGraph (edgeChecker data oldStep) x y pathCode parameter)) := by
  have hn := InternalParameterizedPathCheckerProof.nilAccept (body := body) (Gamma := Gamma)
    (edgeChecker data oldStep) y y parameter
    (PathSupportProof.equalReflexive y)
  obtain ⟨hcons⟩ := InternalParameterizedPathCheckerProof.positiveCons
    (edgeChecker data oldStep) x y pathCode entry z y child parameter hp hc
  obtain ⟨hboth⟩ := andIntro he hn
  exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight hcons) hboth⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateGuardProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFunctionChildCertificateGuardProof
