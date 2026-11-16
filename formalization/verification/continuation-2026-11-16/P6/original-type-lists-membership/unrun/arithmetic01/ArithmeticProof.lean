module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.MemberProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalPairingOrderArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.ArithmeticProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn emb add mul)
open InternalTagArithmeticSupportProof InternalAdditionLawsProof
open InternalSourceInversionSupportProof (onEquality)
open InternalOriginalOrderSyntaxProof InternalOriginalOrderProof
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andRight)
open SourceComputabilityFormulaSupportProof (numeral)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem cancelOrder (s t : OTerm alpha)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess (suc s) (suc t)))) :
    Nonempty (Derivation body Delta (InternalLessThan.strictLess s t)) := by
  apply orderCases Delta (suc s) (suc t) _ h
  intro beta j Theta gap hj he
  simp only [InternalLessThan.strictLess,orderRename]
  obtain ⟨he⟩ := he
  simp only [InternalTagArithmeticSyntaxProof.sucRelabel] at he
  apply actualOriginalOrderIntroduction body beta Theta (s.relabel j) (t.relabel j) gap
  rw [onEquality]
  exact ⟨cancelSuc (trans (symm (leftSuccessor (s.relabel j) (suc gap))) he)⟩

theorem belowOne (s : OTerm alpha)
    (h : Nonempty (Derivation body Delta (InternalLessThan.strictLess s (suc z)))) :
    Nonempty (Derivation body Delta (eqn s z)) := by
  apply InternalOriginalPairingOrderArithmeticProof.weakCases s z _ h
  · obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha s
    exact ⟨Derivation.explosion (Derivation.implicationElimination
      (InternalPositiveUnfoldingSupportProof.weakenClosed hn _) (Derivation.hypothesis List.mem_cons_self))⟩
  · exact ⟨Derivation.hypothesis List.mem_cons_self⟩

theorem singletonZero : Nonempty (Derivation body Delta
    (graph2 InternalListCodec.consCode (numeral 1) (z : OTerm alpha) z)) := by
  obtain ⟨hn⟩ := InternalLeastNumberProof.actualNothingBelowZero body alpha (z : OTerm alpha)
  have hp := InternalPairingSupportProof.pairingOfNotLess z z
    ⟨InternalPositiveUnfoldingSupportProof.weakenClosed hn Delta⟩
  have he : Derivation body Delta (eqn (add (add (mul (z : OTerm alpha) z) z) z) z) :=
    trans (addZero _) (trans (addZero _) (InternalMultiplicationLawsProof.mulZero z))
  have hp0 := outputTransport InternalPairing.pairing (add (add (mul z z) z) z) z ![z,z] ⟨he⟩ hp
  exact InternalListCodecSupportProof.consValue z z z hp0

theorem consNonzero (raw head tail : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail))) :
    Nonempty (Derivation body Delta (eqn raw z).not) :=
  andRight (andRight (InternalListCodecSupportProof.consDestruction raw head tail hc))

theorem membersTransport (raw other allowed : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn raw other)))
    (hm : Nonempty (Derivation body Delta (Targets.allMembers raw allowed))) :
    Nonempty (Derivation body Delta (Targets.allMembers other allowed)) := by
  let theta : Formula (alpha ⊕ Fin 1) := Targets.allMembers (.var (.inr 0)) (allowed.relabel Sum.inl)
  obtain ⟨hm⟩ := hm
  obtain ⟨he⟩ := he
  have hi : Derivation body Delta (InternalClosedPrograms.instantiate theta (emb raw)) := by
    simpa only [theta,InternalClosedPrograms.instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,
      MemberSyntaxProof.membersSubst,InternalTagArithmeticSyntaxProof.varBind,
      InternalTagArithmeticSyntaxProof.liftBind] using hm
  have ho := Derivation.equalityElimination theta (emb raw) (emb other) he hi
  simpa only [theta,InternalClosedPrograms.instantiate,InternalTagArithmeticSyntaxProof.bindEmbedding,
    MemberSyntaxProof.membersSubst,InternalTagArithmeticSyntaxProof.varBind,
    InternalTagArithmeticSyntaxProof.liftBind] using (Nonempty.intro ho)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.ArithmeticProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.ArithmeticProof
