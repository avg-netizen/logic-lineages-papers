module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityExposureProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldOrdinaryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldNumberedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureCommutationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternal
open OriginalLambdaTraversalInternalSubstitutionProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

open InternalAcceptanceSupportProof (programCases)

theorem rawTarget (s t typ raw target head base label nil d cutoff erasedS erasedT erasedRaw erasedBase : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing erasedS typ erasedRaw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor erasedRaw head erasedBase)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing t typ target)))
    (hn : Nonempty (Derivation body Delta (programGraph nilConstructor nil Fin.elim0)))
    (hc : Nonempty (Derivation body Delta
      (programGraph numberedConstructor target ![label,head,typ,base,numeral 0,nil])))
    (hb : Nonempty (Derivation body Delta (graph3 eraseRaw erasedBase d cutoff base)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erasedT d cutoff t))) :
    Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.resultCode erasedT erasedS label)) := by
  apply programCases eraseRaw ![d,cutoff,target] _
  intro beta j Theta erasedTarget hj hv
  have hvec : (fun i : Fin 3 => (![d,cutoff,target] i).relabel j) =
      ![d.relabel j,cutoff.relabel j,target.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k))) i
  rw [hvec] at hv
  simp only [graph2Rename]
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  have ht' := renameInto ht j Theta hj
  have hn' := renameInto hn j Theta hj
  have hc' := renameInto hc j Theta hj
  have hb' := renameInto hb j Theta hj
  have he' := renameInto he j Theta hj
  simp only [graph2Rename] at hp' ho' ht'
  simp only [graph3Rename] at hb' he'
  simp only [programRename,emptyRename] at hn'
  simp only [programRename] at hc'
  have hvec6 : (fun i : Fin 6 => (![label,head,typ,base,numeral 0,nil] i).relabel j) =
      ![label.relabel j,head.relabel j,typ.relabel j,base.relabel j,numeral 0,nil.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (Fin.cases rfl
      (Fin.cases (GuardedSourceSyntaxProof.numeralRename 0 j) (Fin.cases rfl (fun k => Fin.elim0 k)))))) i
  rw [hvec6] at hc'
  have hnil : Nonempty (Derivation body Theta
      (graph3 eraseRaw (nil.relabel j) (d.relabel j) (cutoff.relabel j) (nil.relabel j))) :=
    OriginalRawSyntaxTransportInternalFoldLeafConstructorsProof.nilBackward .erase
      (nil.relabel j) (nil.relabel j) (d.relabel j) (cutoff.relabel j) hn'
      ⟨Derivation.equalityReflexivity (arithmeticEmbedding.onTerm (nil.relabel j))⟩
  have hnumbered := OriginalRawSyntaxTransportInternalFoldNumberedProof.numberedForward .erase
    (target.relabel j) erasedTarget (d.relabel j) (cutoff.relabel j)
    (label.relabel j) (head.relabel j) (typ.relabel j) (base.relabel j) (numeral 0)
    (nil.relabel j) (erasedBase.relabel j) (nil.relabel j) hc' hb' hnil hv
  have hpacked := OriginalRawSyntaxTransportInternalPackedProof.erasePackedForward
    (t.relabel j) (erasedT.relabel j) (typ.relabel j) (target.relabel j)
    erasedTarget (d.relabel j) (cutoff.relabel j) ht' hv he'
  exact PutErasureSupportProof.resultIntro (erasedS.relabel j) (erasedT.relabel j)
    (typ.relabel j) (erasedRaw.relabel j) erasedTarget (head.relabel j)
    (erasedBase.relabel j) (label.relabel j) (nil.relabel j) hp' ho' hpacked hn' hnumbered

theorem commute (s t typ raw head base label d cutoff erasedS erasedT : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hr : Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label)))
    (hs : Nonempty (Derivation body Delta (graph3 erasePackedRaw erasedS d cutoff s)))
    (ht : Nonempty (Derivation body Delta (graph3 erasePackedRaw erasedT d cutoff t))) :
    Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.resultCode erasedT erasedS label)) := by
  apply PutErasureSupportProof.ordinaryExposure s typ raw head base d cutoff erasedS _ hp ho hs
  intro beta j Theta erasedRaw erasedBase hj hpE hoE hbE
  simp only [graph2Rename]
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  have hr' := renameInto hr j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [graph2Rename] at hp' ho' hr'
  simp only [graph3Rename] at ht'
  apply PutValidityExposureProof.exposure (s.relabel j) (t.relabel j) (typ.relabel j)
    (raw.relabel j) (head.relabel j) (base.relabel j) (label.relabel j) _ hp' ho' hr'
  intro beta2 k Psi target nil hk hpT hnT hcT
  simp only [graph2Rename]
  have hpE' := renameInto hpE k Psi hk
  have hoE' := renameInto hoE k Psi hk
  have hbE' := renameInto hbE k Psi hk
  have ht'' := renameInto ht' k Psi hk
  simp only [graph2Rename] at hpE' hoE'
  simp only [graph3Rename] at hbE' ht''
  exact rawTarget ((s.relabel j).relabel k) ((t.relabel j).relabel k)
    ((typ.relabel j).relabel k) ((raw.relabel j).relabel k) target
    ((head.relabel j).relabel k) ((base.relabel j).relabel k) ((label.relabel j).relabel k)
    nil ((d.relabel j).relabel k) ((cutoff.relabel j).relabel k)
    ((erasedS.relabel j).relabel k) ((erasedT.relabel j).relabel k)
    (erasedRaw.relabel k) (erasedBase.relabel k) hpE' hoE' hpT hnT hcT hbE' ht''

theorem actualPutErasureCommutation : PutErasure.ActualPutErasureCommutation := by
  intro body alpha Delta s t typ raw head base label d cutoff erasedS erasedT
  let A := graph2 InternalPairing.pairing s typ raw ⊓
    (graph2 ordinaryConstructor raw head base ⊓
    (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label ⊓
    (graph3 erasePackedRaw erasedS d cutoff s ⊓ graph3 erasePackedRaw erasedT d cutoff t)))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨result⟩ := commute s t typ raw head base label d cutoff erasedS erasedT
    (andLeft h) (andLeft (andRight h)) (andLeft (andRight (andRight h)))
    (andLeft (andRight (andRight (andRight h)))) (andRight (andRight (andRight (andRight h))))
  exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureCommutationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureCommutationProof
