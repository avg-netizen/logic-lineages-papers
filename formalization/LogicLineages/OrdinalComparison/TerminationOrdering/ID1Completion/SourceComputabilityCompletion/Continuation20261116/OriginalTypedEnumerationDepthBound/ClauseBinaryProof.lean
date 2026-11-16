module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.BinaryDispatchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardChoiceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationMembership.GuardPairProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseBinaryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn)
open Continuation20261115
open SourceComputabilityFormulaSupportProof (numeral)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open DispatchFrame
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {n : Nat} {H : Program 1} {arguments : Bool} {body : Positive (Fin 1)}
  {alpha : Type} {Delta : List (Formula alpha)}

theorem atBinary (f : Frame n H arguments body alpha Delta) (tag payload first second : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing f.raw tag payload)))
    (hf : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.firstOf (.projection 0)) first f.raw)))
    (hs : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.secondOf (.projection 0)) second f.raw))) :
    Nonempty (Derivation body Delta (((eqn tag (numeral 2) ⊔ eqn tag (numeral 7)) ⊓ (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)).imp f.conclusion)) := by
  let A := (eqn tag (numeral 2) ⊔ eqn tag (numeral 7)) ⊓ (graph1 (OriginalCodeValidityGuard.check n) (numeral 1) first ⊓ graph1 (OriginalCodeValidityGuard.check n) (numeral 1) second)
  have h : Nonempty (Derivation body (A :: Delta) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have h2 : Nonempty (Derivation body (A :: Delta) ((eqn tag (numeral 2)).imp f.conclusion)) := by
    let T := eqn tag (numeral 2)
    have ht : Nonempty (Derivation body (T :: A :: Delta) T) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := BinaryDispatchProof.application ((f.addHyp A).addHyp T) payload first second
      (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 2 (withHyp (withHyp hp A) T) ht)
      (withHyp (withHyp hf A) T) (withHyp (withHyp hs A) T)
      (withHyp (andLeft (andRight h)) T) (withHyp (andRight (andRight h)) T)
    exact ⟨Derivation.implicationIntroduction d⟩
  have h7 : Nonempty (Derivation body (A :: Delta) ((eqn tag (numeral 7)).imp f.conclusion)) := by
    let T := eqn tag (numeral 7)
    have ht : Nonempty (Derivation body (T :: A :: Delta) T) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨d⟩ := BinaryDispatchProof.cons ((f.addHyp A).addHyp T) payload first second
      (OriginalEnumerationMembership.GuardPairProof.pairLiteral f.raw tag payload 7 (withHyp (withHyp hp A) T) ht)
      (withHyp (withHyp hf A) T) (withHyp (withHyp hs A) T)
      (withHyp (andLeft (andRight h)) T) (withHyp (andRight (andRight h)) T)
    exact ⟨Derivation.implicationIntroduction d⟩
  obtain ⟨ho⟩ := OriginalEnumerationMembership.GuardChoiceProof.orConclusion h2 h7
  obtain ⟨ht⟩ := andLeft h
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationElimination ho ht)⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseBinaryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ClauseBinaryProof
