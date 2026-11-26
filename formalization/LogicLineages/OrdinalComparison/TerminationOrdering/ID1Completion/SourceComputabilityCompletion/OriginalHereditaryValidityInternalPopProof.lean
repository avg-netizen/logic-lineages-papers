module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPopProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof OriginalLambdaConstructorGraphSyntaxProof
open OriginalHereditaryValidityInternalBranchProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem popForward (s t m : Program 2)
    (state workCode frame raw parameter restCode tag out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw)))
    (h2 : Nonempty (Derivation body Delta (equal tag (numeral 2)).not))
    (h1 : Nonempty (Derivation body Delta (equal tag (numeral 1)).not))
    (ho : Nonempty (Derivation body Delta (graph1 (transition s t m) out state))) :
    Nonempty (Derivation body Delta (StateGraph out (numeral 1) restCode)) := by
  have hp := popElim state tag out (frameTag state workCode frame raw parameter restCode tag hs ht)
    h2 h1 (acceptingVisitElim s t m state workCode frame raw parameter restCode out hs hn ho)
  exact binaryRecover InternalPairing.pairing (InternalLessThan.constantOne 1) rest
    out (numeral 1) restCode (Fin.cons state Fin.elim0) hp
    (InternalLessThanSupportProof.oneConstantValue _) (frameRest state workCode frame raw parameter restCode hs)

theorem popBackward (s t m : Program 2)
    (state workCode frame raw parameter restCode tag out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag tag raw)))
    (h2 : Nonempty (Derivation body Delta (equal tag (numeral 2)).not))
    (h1 : Nonempty (Derivation body Delta (equal tag (numeral 1)).not))
    (ho : Nonempty (Derivation body Delta (StateGraph out (numeral 1) restCode))) :
    Nonempty (Derivation body Delta (graph1 (transition s t m) out state)) := by
  apply acceptingVisitIntro s t m state workCode frame raw parameter restCode out hs hn
  apply popIntro state tag out (frameTag state workCode frame raw parameter restCode tag hs ht) h2 h1
  exact binaryValue InternalPairing.pairing (InternalLessThan.constantOne 1) rest
    out (numeral 1) restCode (Fin.cons state Fin.elim0) ho
    (InternalLessThanSupportProof.oneConstantValue _) (frameRest state workCode frame raw parameter restCode hs)

theorem actualOriginalHereditaryPopTransition :
    OriginalHereditaryValidityInternalTargets.ActualOriginalHereditaryPopTransition := by
  intro body s t m alpha state workCode frame raw parameter restCode tag out
  let C := StateFrame state workCode frame raw parameter restCode ⊓
    (graph1 (nodeCheck s t m) (numeral 1) state ⊓
      (graph1 OriginalLambdaConstructor.tag tag raw ⊓
        ((equal tag (numeral 2)).not ⊓ (equal tag (numeral 1)).not)))
  let G := graph1 (transition s t m) out state
  let R := StateGraph out (numeral 1) restCode
  have hcG : Nonempty (Derivation body [G,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation body [R,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := popForward s t m state workCode frame raw parameter restCode tag out
    (andLeft hcG) (andLeft (andRight hcG)) (andLeft (andRight (andRight hcG)))
    (andLeft (andRight (andRight (andRight hcG))))
    (andRight (andRight (andRight (andRight hcG)))) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := popBackward s t m state workCode frame raw parameter restCode tag out
    (andLeft hcR) (andLeft (andRight hcR)) (andLeft (andRight (andRight hcR)))
    (andLeft (andRight (andRight (andRight hcR))))
    (andRight (andRight (andRight (andRight hcR)))) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPopProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalPopProof
