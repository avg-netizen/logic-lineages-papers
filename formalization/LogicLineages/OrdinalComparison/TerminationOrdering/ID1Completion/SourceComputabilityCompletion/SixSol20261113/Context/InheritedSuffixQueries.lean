module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.TermSuffixIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedSuffixQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z zRelabel)
open InternalTagArithmeticSupportProof (symm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open SixSol20261112.Context
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem withInherited
    (count typ raw parameter c gamma rawJob typed job rawJobs annotatedPrefix full annotatedSuffix : OTerm alpha)
    (psi : Formula alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
    (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job z typed)))
    (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) count raw)))
    (he : Nonempty (Derivation body Delta (graph2 OriginalHereditaryExpansion.expansion rawJobs raw parameter)))
    (hscan : Nonempty (Derivation body Delta (graph5 OriginalHereditaryAnnotatedExpansion.scan annotatedPrefix count z typ raw rawJobs)))
    (hfull : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion full job)))
    (happend : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append full annotatedPrefix annotatedSuffix)))
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (deletionJobs : OTerm beta),
      (∀ f ∈ Delta, f.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (graph2 OriginalHereditaryExpansion.deletionJobs deletionJobs (raw.relabel j) (parameter.relabel j))) →
      Nonempty (Derivation body Theta (graph2 (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob)
        (annotatedSuffix.relabel j) deletionJobs (typ.relabel j))) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  let childP : Program 3 := .composition OriginalHereditaryExpansion.childJobs ![.projection 0,.projection 1]
  let deletionP : Program 3 := .composition OriginalHereditaryExpansion.deletionJobs ![.projection 0,.projection 1]
  let inheritedP : Program 3 := .composition (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) ![deletionP,.projection 2]
  let qs : Fin 3 → Program 3 := ![childP,deletionP,inheritedP]
  let xs : Fin 3 → OTerm alpha := ![raw,parameter,typ]
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
  intro beta j ys Theta hi hq
  let xx : Fin 3 → OTerm beta := ![raw.relabel j,parameter.relabel j,typ.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  rw [hx] at hq
  have hchild := binaryRecover OriginalHereditaryExpansion.childJobs (.projection 0) (.projection 1)
    (ys 0) (raw.relabel j) (parameter.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have hdeletion := binaryRecover OriginalHereditaryExpansion.deletionJobs (.projection 0) (.projection 1)
    (ys 1) (raw.relabel j) (parameter.relabel j) xx (hq 1) (projectionValue 0 xx) (projectionValue 1 xx)
  have hinherited := binaryRecover (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob) deletionP (.projection 2)
    (ys 2) (ys 1) (typ.relabel j) xx (hq 2) (hq 1) (projectionValue 2 xx)
  have hp' := renameInto hp j Theta hi
  have hr' := renameInto hr j Theta hi
  have ht' := renameInto ht j Theta hi
  have hj' := renameInto hj j Theta hi
  have ha' := renameInto ha j Theta hi
  have he' := renameInto he j Theta hi
  have hscan' := renameInto hscan j Theta hi
  have hfull' := renameInto hfull j Theta hi
  have happend' := renameInto happend j Theta hi
  simp only [graph1Rename,graph2Rename,graph5Rename,zRelabel] at hp' hr' ht' hj' ha' he' hscan' hfull' happend'
  have hrawAppend := binaryRecover InternalApplicationValidityStackAppend.append
    OriginalHereditaryExpansion.childJobs OriginalHereditaryExpansion.deletionJobs
    (rawJobs.relabel j) (ys 0) (ys 1) (Fin.cons (raw.relabel j) (Fin.cons (parameter.relabel j) Fin.elim0)) he' hchild hdeletion
  have hsplit := TermSuffixIdentityProof.split body beta Theta (count.relabel j) (typ.relabel j) (raw.relabel j)
    (parameter.relabel j) (c.relabel j) (gamma.relabel j) (rawJob.relabel j) (typed.relabel j) (job.relabel j)
    (ys 0) (ys 1) (rawJobs.relabel j) (annotatedPrefix.relabel j) (ys 2) (full.relabel j)
    hp' hr' ht' hj' ha' hchild hdeletion hrawAppend hscan' hinherited hfull'
  obtain ⟨heq⟩ := AppendIdentityProof.actualLeftCancellation body beta Theta
    (annotatedPrefix.relabel j) (annotatedSuffix.relabel j) (ys 2) (full.relabel j) happend' hsplit
  have hm := outputTransport (InternalListMap.map (k := 1) InheritedMapDefinitions.inheritedJob)
    (ys 2) (annotatedSuffix.relabel j) (Fin.cons (ys 1) (Fin.cons (typ.relabel j) Fin.elim0)) ⟨symm heq⟩ hinherited
  exact next beta j Theta (ys 1) hi hdeletion hm
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedSuffixQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.InheritedSuffixQueries
