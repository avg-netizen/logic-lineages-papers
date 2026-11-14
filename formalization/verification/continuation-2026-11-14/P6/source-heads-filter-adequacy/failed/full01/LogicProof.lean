module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.StepSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.LogicProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof InternalPositiveUnfoldingSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open TwoSol20261113.CalibratedPrimary.Membership
open TwoSol20261113.CalibratedPrimary.MembershipInternalProof
open SourceComputabilityFormulaSupportProof (numeral)
open ConcreteHeadMoveLayer.SupportProof (Maps andMap)
open StepSupportProof Induction
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem weak {P : Formula alpha} (h : Nonempty (Derivation body Delta P))
    (Theta : List (Formula alpha)) (hi : ∀ a ∈ Delta, a ∈ Theta) :
    Nonempty (Derivation body Theta P) := by
  obtain ⟨d⟩ := h
  exact ⟨Derivation.weakening hi d⟩

theorem iffTransfer {A B C D : Formula alpha}
    (old : Nonempty (Derivation body Delta (A.imp B ⊓ B.imp A)))
    (ca : Maps (body := body) Delta C A) (ac : Maps (body := body) Delta A C)
    (bd : Maps (body := body) Delta B D) (db : Maps (body := body) Delta D B) :
    Nonempty (Derivation body Delta (C.imp D ⊓ D.imp C)) := by
  apply andIntro
  · have hi : ∀ a ∈ Delta, a ∈ C :: Delta := fun _ ha => List.mem_cons_of_mem _ ha
    obtain ⟨h⟩ := ca _ hi ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨o⟩ := weak old _ hi
    obtain ⟨d⟩ := bd _ hi ⟨Derivation.implicationElimination (Derivation.conjunctionLeft o) h⟩
    exact ⟨Derivation.implicationIntroduction d⟩
  · have hi : ∀ a ∈ Delta, a ∈ D :: Delta := fun _ ha => List.mem_cons_of_mem _ ha
    obtain ⟨h⟩ := db _ hi ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨o⟩ := weak old _ hi
    obtain ⟨d⟩ := ac _ hi ⟨Derivation.implicationElimination (Derivation.conjunctionRight o) h⟩
    exact ⟨Derivation.implicationIntroduction d⟩

theorem memberEqual (out rest needle : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn out rest))) :
    Maps (body := body) Delta (graph2 contains (numeral 1) out needle) (graph2 contains (numeral 1) rest needle) ∧
    Maps (body := body) Delta (graph2 contains (numeral 1) rest needle) (graph2 contains (numeral 1) out needle) := by
  constructor
  · intro Theta hi h
    exact headTransport contains (numeral 1) out rest (Fin.cons needle Fin.elim0) (weak he Theta hi) h
  · intro Theta hi h
    obtain ⟨e⟩ := weak he Theta hi
    exact headTransport contains (numeral 1) rest out (Fin.cons needle Fin.elim0) ⟨symm e⟩ h

theorem memberMiss (raw head tail needle : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hn : Nonempty (Derivation body Delta (equal head needle).not)) :
    Maps (body := body) Delta (graph2 contains (numeral 1) raw needle) (graph2 contains (numeral 1) tail needle) ∧
    Maps (body := body) Delta (graph2 contains (numeral 1) tail needle) (graph2 contains (numeral 1) raw needle) := by
  constructor
  · intro Theta hi h
    exact PrimaryMembership.Proof.missRecover raw head tail needle (numeral 1) (weak hc Theta hi) (weak hn Theta hi) h
  · intro Theta hi h
    exact containsMiss raw head tail needle (numeral 1) (weak hc Theta hi) (weak hn Theta hi) h

theorem missResult (raw head tail symbols needle types out rest value : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
    (hn : Nonempty (Derivation body Delta (equal head needle).not))
    (old : Nonempty (Derivation body Delta (result tail symbols needle types rest value)))
    (ca : Maps (body := body) Delta (graph2 contains (numeral 1) out needle) (graph2 contains (numeral 1) rest needle))
    (ac : Maps (body := body) Delta (graph2 contains (numeral 1) rest needle) (graph2 contains (numeral 1) out needle)) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  have ms := memberMiss raw head tail needle hc hn
  exact iffTransfer old ca ac
    (andMap ms.2 (ConcreteHeadMoveLayer.SupportProof.reflexive _ _))
    (andMap ms.1 (ConcreteHeadMoveLayer.SupportProof.reflexive _ _))

theorem zeroResult (raw tail symbols needle types out rest value : OTerm alpha)
    (he : Nonempty (Derivation body Delta (eqn out rest)))
    (hz : Nonempty (Derivation body Delta (eqn value z)))
    (old : Nonempty (Derivation body Delta (result tail symbols needle types rest value))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  have dead (a b : OTerm alpha) : Maps (body := body) Delta (qualifies a needle value) (qualifies b needle value) := by
    intro Theta hi h
    obtain ⟨hn⟩ := andRight h
    obtain ⟨hz⟩ := weak hz Theta hi
    exact ⟨Derivation.explosion (Derivation.implicationElimination hn hz)⟩
  have mm := memberEqual out rest needle he
  exact iffTransfer old mm.1 mm.2 (dead tail raw) (dead raw tail)

theorem trueResult (raw symbols needle types out value : OTerm alpha)
    (hm : Nonempty (Derivation body Delta (graph2 contains (numeral 1) out needle)))
    (hq : Nonempty (Derivation body Delta (qualifies raw needle value))) :
    Nonempty (Derivation body Delta (result raw symbols needle types out value)) := by
  apply andIntro
  · obtain ⟨h⟩ := withHyp hq (graph2 contains (numeral 1) out needle)
    exact ⟨Derivation.implicationIntroduction h⟩
  · obtain ⟨h⟩ := withHyp hm (qualifies raw needle value)
    exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.LogicProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.SourceHeadsFilterAdequacy.LogicProof
