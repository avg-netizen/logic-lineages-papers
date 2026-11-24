module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseMemberConsProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseBranchFlagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFlagsConsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalControlGraphSupportProof (headTransport valueUnique)
open InternalTagArithmeticSyntaxProof (z suc eqn)
open InternalTagArithmeticSupportProof (sucNeZeroApply)
open InternalQuotientComparisonProof (orLeft orRight)
open InternalRawListRecursion (recGraph)
open InternalRawListRecursionProof (nilRecover)
open InternalAcceptanceConjunctionProof (constantZeroValue)
open SourceComputabilityCompletion.OriginalTypedDecoderInternalBranchProof (orCases)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep scratchMember)
open NumberedWindowInternalLiteralScratchErase (state)
open NumberedWindowInternalLiteralScratchEraseCoordinatesProof (nilCoordinates)
open NumberedWindowInternalLiteralScratchEraseBranchFlagsProof (headHit tailHit bothMiss)
open NumberedWindowInternalLiteralScratchEraseMemberConsProof (absentBranchImpossible)

attribute [local irreducible] programGraph
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Bit is genuinely zero or one, and the actual member graph guarantees one. -/
def flags (raw needle bit : OTerm alpha) : Formula alpha :=
  (eqn bit z ⊔ eqn bit (suc z)) ⊓ ((memberGraph raw needle).imp (eqn bit (suc z)))

private theorem tapeTwo (c n : OTerm alpha) :
    (![c,n] : Fin 2 → OTerm alpha) = Fin.cons c (![n] : Fin 1 → OTerm alpha) := by
  funext i
  exact Fin.cases rfl (Fin.cases rfl (fun q => Fin.elim0 q)) i

theorem nilFlags (needle acc bit rest : OTerm alpha)
    (ha : Nonempty (Derivation body Delta (graph2 state acc z needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc bit rest))) :
    Nonempty (Derivation body Delta (flags z needle bit)) := by
  obtain ⟨coords⟩ := nilCoordinates needle acc bit rest ha hap
  let M := memberGraph z needle
  have hm : Derivation body (M :: Delta) M := Derivation.hypothesis List.mem_cons_self
  have run : Nonempty (Derivation body (M :: Delta) (recGraph memberBase memberStep (suc z) z ![needle])) := by
    simpa only [M,memberGraph,tapeTwo,recGraph,scratchMember] using (Nonempty.intro hm)
  have dead := nilRecover memberBase memberStep (suc z) ![needle] run
  obtain ⟨absurd⟩ := valueUnique memberBase (suc z) z ![needle] dead (constantZeroValue ![needle])
  exact ⟨Derivation.conjunctionIntroduction (orLeft (Derivation.conjunctionLeft coords))
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply absurd)))⟩

private theorem oneFlags (raw needle bit : OTerm alpha)
    (h : Nonempty (Derivation body Delta (eqn bit (suc z)))) :
    Nonempty (Derivation body Delta (flags raw needle bit)) := by
  obtain ⟨d⟩ := h
  obtain ⟨kept⟩ := withHyp (Nonempty.intro d) (memberGraph raw needle)
  exact ⟨Derivation.conjunctionIntroduction (orRight d) (Derivation.implicationIntroduction kept)⟩

theorem consFlags (list head tail needle acc tailBit rest actual bit remaining : OTerm alpha)
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode list head tail)))
    (ht : Nonempty (Derivation body Delta (graph2 state acc tail needle)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing acc tailBit rest)))
    (ih : Nonempty (Derivation body Delta (flags tail needle tailBit)))
    (ha : Nonempty (Derivation body Delta (graph2 state actual list needle)))
    (hap : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing actual bit remaining))) :
    Nonempty (Derivation body Delta (flags list needle bit)) := by
  have cases : Nonempty (Derivation body Delta (eqn tailBit z ⊔ eqn tailBit (suc z))) := andLeft ih
  apply orCases cases
  · let E := eqn tailBit z
    have e : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp0 := headTransport InternalPairing.pairing acc tailBit z (Fin.cons rest Fin.elim0) e (withHyp hp E)
    let H := eqn head needle
    apply formulaCases H
    · exact oneFlags list needle bit (headHit list head tail needle acc rest actual bit remaining
        (withHyp (withHyp hc E) H) (withHyp (withHyp ht E) H) (withHyp hp0 H)
        ⟨Derivation.hypothesis List.mem_cons_self⟩ (withHyp (withHyp ha E) H) (withHyp (withHyp hap E) H))
    · let N := H.not
      have hn : Nonempty (Derivation body (N :: E :: Delta) N) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hc' := withHyp (withHyp hc E) N
      have ht' := withHyp (withHyp ht E) N
      have ha' := withHyp (withHyp ha E) N
      have hap' := withHyp (withHyp hap E) N
      obtain ⟨hzero⟩ := bothMiss list head tail needle acc rest actual bit remaining hc' ht'
        (withHyp hp0 N) hn ha' hap'
      let M := memberGraph list needle
      have hm : Nonempty (Derivation body (M :: N :: E :: Delta) M) := ⟨Derivation.hypothesis List.mem_cons_self⟩
      have hi : Nonempty (Derivation body (M :: N :: E :: Delta)
          ((memberGraph tail needle).imp (eqn tailBit (suc z)))) :=
        andRight (withHyp (withHyp (withHyp ih E) N) M)
      obtain ⟨bad⟩ := absentBranchImpossible list head tail needle tailBit (eqn bit (suc z))
        (withHyp hc' M) hm (withHyp hn M) (withHyp (withHyp e N) M) hi
      exact ⟨Derivation.conjunctionIntroduction (orLeft hzero) (Derivation.implicationIntroduction bad)⟩
  · let E := eqn tailBit (suc z)
    have e : Nonempty (Derivation body (E :: Delta) E) := ⟨Derivation.hypothesis List.mem_cons_self⟩
    have hp1 := headTransport InternalPairing.pairing acc tailBit (suc z) (Fin.cons rest Fin.elim0) e (withHyp hp E)
    exact oneFlags list needle bit (tailHit list head tail needle acc rest actual bit remaining
      (withHyp hc E) (withHyp ht E) hp1 (withHyp ha E) (withHyp hap E))

#print axioms nilFlags
#print axioms consFlags
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralScratchEraseFlagsConsProof
