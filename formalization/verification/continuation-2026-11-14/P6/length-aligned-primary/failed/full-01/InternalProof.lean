module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentPrimary.InternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.PrimaryFiniteDescent.CutoffProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalAcceptanceSupportProof InternalGraphCompositionFunctionalityProof
open InternalRecursionGraphStepSyntaxProof InternalTagArithmeticSyntaxProof
open InternalTagArithmeticSupportProof SourceComputabilityFormulaSupportProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp formulaCases)
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalBetaTotalityProof InternalQuotientComparisonProof
open TwoSol20261113.CalibratedPrimary.Membership
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

open InternalAcceptanceBranchProof InternalAcceptanceConjunctionProof
open PrimaryMonotonicity.InclusionProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem internalCountLength : Targets.InternalCountLength := by
  intro P body alpha Delta seed parameter pool size hp hc
  apply compositionRecover length (fun _ : Fin 1 => P) size ![seed,parameter]
    (Fin.cons pool Fin.elim0) hc
  intro i
  obtain rfl := Fin.eq_zero i
  exact hp

theorem runCutoff (E : Program 3) (size pool seed parameter out next : OTerm alpha)
    (hlen : Nonempty (Derivation body Delta (lengthGraph size pool)))
    (hr : Nonempty (Derivation body Delta (graph4 (PrimaryIteration.run E) out size pool seed parameter)))
    (he : Nonempty (Derivation body Delta (graph3 (PrimaryExpansion.expand E) next pool out parameter))) :
    Nonempty (Derivation body Delta (PrimaryMonotonicity.included next out)) := by
  apply programCases InternalListCodec.consCode (Fin.cons seed (Fin.cons z Fin.elim0)) _
  intro beta j Theta singleton hj hs
  rw [includedRename]
  simp only [consTermRename,emptyRename,zRelabel] at hs
  have hr' := renameInto hr j Theta hj
  rw [graph4Rename] at hr'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  have hlen' := renameInto hlen j Theta hj
  rw [lengthRename] at hlen'
  let xs : Fin 4 → OTerm beta := ![size.relabel j,pool.relabel j,seed.relabel j,parameter.relabel j]
  let singletonP : Program 4 := .composition InternalListCodec.consCode
    ![.projection 2,InternalAcceptance.constantZero 4]
  have hsingle := binaryValue InternalListCodec.consCode (.projection 2)
    (InternalAcceptance.constantZero 4) singleton (seed.relabel j) z xs hs
    (projectionValue 2 xs) (constantZeroValue xs)
  have hi : Nonempty (Derivation body Theta
      (graph4 (PrimaryIteration.iterate E) (out.relabel j) (size.relabel j) (pool.relabel j)
        singleton (parameter.relabel j))) := by
    apply compositionRecover (PrimaryIteration.iterate E) ![.projection 0,.projection 1,singletonP,.projection 3]
      (out.relabel j) xs ![size.relabel j,pool.relabel j,singleton,parameter.relabel j] hr'
    intro i
    exact Fin.cases (projectionValue 0 xs) (Fin.cases (projectionValue 1 xs)
      (Fin.cases hsingle (Fin.cases (projectionValue 3 xs) (fun k => Fin.elim0 k)))) i
  exact PrimaryFiniteDescent.CutoffProof.literalLengthCutoff E body beta Theta (size.relabel j)
    (pool.relabel j) singleton (parameter.relabel j) (out.relabel j) (next.relabel j) hlen' hi he'

theorem internalPrimaryStability : Targets.InternalPrimaryStability := by
  intro T P E body alpha Delta seed parameter pool out next hT hP hL he
  apply programCases (countOfPool P) (Fin.cons seed (Fin.cons parameter Fin.elim0)) _
  intro beta j Theta size hj hc
  rw [includedRename]
  simp only [consTermRename,emptyRename] at hc
  have hT' := renameInto hT j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hT'
  have hP' := renameInto hP j Theta hj
  rw [graph2Rename] at hP'
  have hL' := renameInto hL j Theta hj
  rw [graph2Rename] at hL'
  have he' := renameInto he j Theta hj
  rw [graph3Rename] at he'
  let s := seed.relabel j
  let p := parameter.relabel j
  have hlen := internalCountLength P body beta Theta s p (pool.relabel j) size hP' hc
  have hr := successorBranchElim T (InternalAcceptance.constantZero 2)
    (.composition (PrimaryIteration.run E) ![countOfPool P,P,.projection 0,.projection 1])
    (out.relabel j) z ![s,p] hT' hL'
  have hi : Nonempty (Derivation body Theta
      (graph4 (PrimaryIteration.run E) (out.relabel j) size (pool.relabel j) s p)) := by
    apply compositionRecover (PrimaryIteration.run E) ![countOfPool P,P,.projection 0,.projection 1]
      (out.relabel j) ![s,p] ![size,pool.relabel j,s,p] hr
    intro i
    exact Fin.cases hc (Fin.cases hP' (Fin.cases (projectionValue 0 ![s,p])
      (Fin.cases (projectionValue 1 ![s,p]) (fun k => Fin.elim0 k)))) i
  exact runCutoff E size (pool.relabel j) s p (out.relabel j) (next.relabel j) hlen hi he'

theorem internalEdgeClosure : Targets.InternalEdgeClosure := by
  intro T P E body alpha Delta seed parameter pool out source candidate hT hP hL hs hp hedge
  apply programCases (PrimaryExpansion.expand E) (Fin.cons pool (Fin.cons out (Fin.cons parameter Fin.elim0))) _
  intro beta j Theta next hj he
  simp only [graph2Rename,numeral,sucRelabel,zRelabel]
  simp only [consTermRename,emptyRename] at he
  have hT' := renameInto hT j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hT'
  have hP' := renameInto hP j Theta hj
  rw [graph2Rename] at hP'
  have hL' := renameInto hL j Theta hj
  rw [graph2Rename] at hL'
  have hs' := renameInto hs j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hs'
  have hp' := renameInto hp j Theta hj
  simp only [graph2Rename,numeral,sucRelabel,zRelabel] at hp'
  have hedge' := renameInto hedge j Theta hj
  simp only [graph3Rename,numeral,sucRelabel,zRelabel] at hedge'
  have hstable := internalPrimaryStability T P E body beta Theta (seed.relabel j)
    (parameter.relabel j) (pool.relabel j) (out.relabel j) next hT' hP' hL' he
  have hm := PrimaryEdgeInclusion.Proof.expansionEdgeInclusion E body beta Theta (pool.relabel j)
    (out.relabel j) (source.relabel j) (candidate.relabel j) (parameter.relabel j) next hs' hp' hedge' he
  exact eliminate next (out.relabel j) (candidate.relabel j) hstable hm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.LengthAlignedPrimary.InternalProof
