module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalResultApplicationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalApplicationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalLambdaConstructorGraphSyntaxProof OriginalHereditaryValidityInternalBranchProof
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalHereditaryValidity OriginalHereditaryValidityInternal
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem applicationForward (s t m : Program 2)
    (state workCode frame raw parameter restCode out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (ho : Nonempty (Derivation body Delta (graph1 (transition s t m) out state))) :
    Nonempty (Derivation body Delta (ApplicationResult state out parameter restCode)) :=
  OriginalHereditaryValidityInternalResultApplicationProof.applicationForward state out parameter restCode
    (frameParameter state workCode frame raw parameter restCode hs)
    (frameRest state workCode frame raw parameter restCode hs)
    (applicationElim state out (frameTag state workCode frame raw parameter restCode (numeral 2) hs ht)
      (acceptingVisitElim s t m state workCode frame raw parameter restCode out hs hn ho))

theorem applicationBackward (s t m : Program 2)
    (state workCode frame raw parameter restCode out : OTerm alpha)
    (hs : Nonempty (Derivation body Delta (StateFrame state workCode frame raw parameter restCode)))
    (hn : Nonempty (Derivation body Delta (graph1 (nodeCheck s t m) (numeral 1) state)))
    (ht : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 2) raw)))
    (ho : Nonempty (Derivation body Delta (ApplicationResult state out parameter restCode))) :
    Nonempty (Derivation body Delta (graph1 (transition s t m) out state)) :=
  acceptingVisitIntro s t m state workCode frame raw parameter restCode out hs hn
    (applicationIntro state out (frameTag state workCode frame raw parameter restCode (numeral 2) hs ht)
      (OriginalHereditaryValidityInternalResultApplicationProof.applicationBackward state out parameter restCode
        (frameParameter state workCode frame raw parameter restCode hs)
        (frameRest state workCode frame raw parameter restCode hs) ho))

theorem actualOriginalHereditaryApplicationTransition :
    OriginalHereditaryValidityInternalTargets.ActualOriginalHereditaryApplicationTransition := by
  intro body s t m alpha state workCode frame raw parameter restCode out
  let C := StateFrame state workCode frame raw parameter restCode ⊓
    (graph1 (nodeCheck s t m) (numeral 1) state ⊓ graph1 OriginalLambdaConstructor.tag (numeral 2) raw)
  let G := graph1 (transition s t m) out state
  let R := ApplicationResult state out parameter restCode
  have hcG : Nonempty (Derivation body [G,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  have hcR : Nonempty (Derivation body [R,C] C) :=
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
  obtain ⟨hf⟩ := applicationForward s t m state workCode frame raw parameter restCode out
    (andLeft hcG) (andLeft (andRight hcG)) (andRight (andRight hcG))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := applicationBackward s t m state workCode frame raw parameter restCode out
    (andLeft hcR) (andLeft (andRight hcR)) (andRight (andRight hcR))
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction hf) (Derivation.implicationIntroduction hb))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryValidityInternalApplicationProof
