module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureCommutationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutFinalStepProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutValidityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransport
open InternalAcceptanceSupportProof (programCases)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open UniformCertificateCompletion PutIntegration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem literalWitness (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (s t parameter typ raw head base label : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P)) (numeral 1) s parameter)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (hr : Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.resultCode t s label))) :
    Nonempty (Derivation body Delta (PutErasure.Witness p H G W P s t parameter label)) := by
  apply programCases SixSol20261112.Erasure.PutRoot.certificateCode ![s,label] _
  intro beta j Theta cert hj hc
  have hvec : (fun i : Fin 2 => (![s,label] i).relabel j) = ![s.relabel j,label.relabel j] := by
    funext i
    exact Fin.cases rfl (Fin.cases rfl (fun k => Fin.elim0 k)) i
  rw [hvec] at hc
  rw [PutErasureSyntaxProof.witnessRename]
  have hs' := renameInto hs j Theta hj
  have hp' := renameInto hp j Theta hj
  have ho' := renameInto ho j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,numeralRename] at hs' hp' ho' hr'
  have hw := PutFinalStepProof.step p H G W P (s.relabel j) (t.relabel j) cert
    (parameter.relabel j) (typ.relabel j) (raw.relabel j) (head.relabel j)
    (base.relabel j) (label.relabel j) hs' hp' ho' hr' hc
  exact PutErasureSyntaxProof.witnessIntro p H G W P (s.relabel j) (t.relabel j)
    (parameter.relabel j) (label.relabel j) cert (andIntro hc hw)

theorem transportedWitness (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (s typ raw head base label d cutoff erasedS erasedT newParam : OTerm alpha)
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P)) (numeral 1) erasedS newParam)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing s typ raw)))
    (ho : Nonempty (Derivation body Delta (graph2 ordinaryConstructor raw head base)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erasedS d cutoff s)))
    (hr : Nonempty (Derivation body Delta (graph2 SixSol20261112.Erasure.PutRoot.resultCode erasedT erasedS label))) :
    Nonempty (Derivation body Delta (PutErasure.Witness p H G W P erasedS erasedT newParam label)) := by
  apply PutErasureSupportProof.ordinaryExposure s typ raw head base d cutoff erasedS _ hp ho he
  intro beta j Theta erasedRaw erasedBase hj hp' ho' _hb
  rw [PutErasureSyntaxProof.witnessRename]
  have hs' := renameInto hs j Theta hj
  have hr' := renameInto hr j Theta hj
  simp only [graph2Rename,numeralRename] at hs' hr'
  exact literalWitness p H G W P (erasedS.relabel j) (erasedT.relabel j) (newParam.relabel j)
    (typ.relabel j) erasedRaw (head.relabel j) erasedBase (label.relabel j) hs' hp' ho' hr'

theorem eraseValidity (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (s erasedS d cutoff gamma extended c oldParam newParam : OTerm alpha)
    (hi : Nonempty (Derivation body Delta (OriginalContextInsertion.Insert d cutoff gamma extended)))
    (he : Nonempty (Derivation body Delta (graph3 erasePackedRaw erasedS d cutoff s)))
    (hop : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing oldParam c extended)))
    (hnp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParam c gamma)))
    (hs : Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P)) (numeral 1) s oldParam))) :
    Nonempty (Derivation body Delta
      (graph2 (InternalOriginalUniformDescentSelection.validity (finalData p H G W P)) (numeral 1) erasedS newParam)) := by
  let q := seed p H G W
  have hsource := iffForward
    (SixSol20261112.Integration.FinalErasureProof.finalSource q H G W P body alpha Delta
      (numeral 1) ![s,oldParam]) hs
  have hout := OriginalPackedSourceErasureProof.actualOriginalPackedSourceErasure body alpha Delta
    H G (InternalOriginalUniformContextMembership.contextMember p.base.member) W
    s erasedS d cutoff gamma extended c oldParam newParam hi he hop hnp hsource
  exact iffBackward
    (SixSol20261112.Integration.FinalErasureProof.finalSource q H G W P body alpha Delta
      (numeral 1) ![erasedS,newParam]) hout

theorem actualFinalPutErasure : PutErasure.ActualFinalPutErasure := by
  intro p H G W P body alpha Delta s t cert oldParam newParam typ raw head base label gamma extended d cutoff c erasedS erasedT
  let A := Fields p H G W P s t cert oldParam typ raw head base label ⊓
    (OriginalContextInsertion.Insert d cutoff gamma extended ⊓
    (graph2 InternalPairing.pairing oldParam c extended ⊓
    (graph2 InternalPairing.pairing newParam c gamma ⊓
    (graph3 erasePackedRaw erasedS d cutoff s ⊓ graph3 erasePackedRaw erasedT d cutoff t))))
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hf := andLeft h
  have hs := andLeft hf
  have hp := andLeft (andRight hf)
  have ho := andLeft (andRight (andRight hf))
  have hr := andLeft (andRight (andRight (andRight hf)))
  have hi := andLeft (andRight h)
  have hop := andLeft (andRight (andRight h))
  have hnp := andLeft (andRight (andRight (andRight h)))
  have hes := andLeft (andRight (andRight (andRight (andRight h))))
  have het := andRight (andRight (andRight (andRight (andRight h))))
  have hsE := eraseValidity p H G W P s erasedS d cutoff gamma extended c oldParam newParam hi hes hop hnp hs
  have hrE := PutErasureCommutationProof.commute s t typ raw head base label d cutoff erasedS erasedT hp ho hr hes het
  have hw := transportedWitness p H G W P s typ raw head base label d cutoff erasedS erasedT newParam hsE hp ho hes hrE
  have hsource := iffForward
    (SixSol20261112.Integration.FinalErasureProof.finalSource (seed p H G W) H G W P body alpha (A :: Delta)
      (numeral 1) ![s,oldParam]) hs
  have htarget := PutValidityPackedProof.packed H G
    (InternalOriginalUniformContextMembership.contextMember p.base.member) W
    s t oldParam typ raw head base label hsource hp ho hr
  have ht := iffBackward
    (SixSol20261112.Integration.FinalErasureProof.finalSource (seed p H G W) H G W P body alpha (A :: Delta)
      (numeral 1) ![t,oldParam]) htarget
  have htE := eraseValidity p H G W P t erasedT d cutoff gamma extended c oldParam newParam hi het hop hnp ht
  obtain ⟨result⟩ := andIntro hsE (andIntro htE hw)
  exact ⟨Derivation.implicationIntroduction result⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.PutErasureProof
