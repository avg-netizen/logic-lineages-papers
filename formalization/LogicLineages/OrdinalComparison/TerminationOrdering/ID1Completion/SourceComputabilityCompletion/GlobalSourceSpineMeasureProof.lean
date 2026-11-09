module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.PositiveSpineRulesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineMeasureProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalTagArithmeticSyntaxProof (OTerm)
open SourceComputabilityCompletion.TypedSpine
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

theorem payloadMeasure (x payload mark : OTerm α)
    (hx : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload x)))
    (hm : Nonempty (Derivation body Gamma (graph1 objectMeasure mark x))) :
    Nonempty (Derivation body Gamma (BottomSpineMeasure.graph mark payload)) :=
  unaryRecover BottomSpineMeasure.measure InternalUnpair.right mark payload (Fin.cons x Fin.elim0) hm hx

theorem objectMeasureValue (x payload mark : OTerm α)
    (hx : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right payload x)))
    (hm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph mark payload))) :
    Nonempty (Derivation body Gamma (graph1 objectMeasure mark x)) :=
  unaryValue BottomSpineMeasure.measure InternalUnpair.right mark payload (Fin.cons x Fin.elim0) hm hx

/-- The literal positive guard gives actual strict depth decrease. The
payload graphs are original object coordinates; neither a semantic spine
predicate nor a Boolean assumption about arbitrary marks is used. -/
theorem guardedProgress (edge : Program 4)
    (f g witness parameter fp gp fm gm fd gd : OTerm α)
    (hf : Nonempty (Derivation body Gamma (marked f fm fd)))
    (hfp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right fp f)))
    (hgp : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right gp g)))
    (hgm : Nonempty (Derivation body Gamma (BottomSpineMeasure.graph gm gp)))
    (hgd : Nonempty (Derivation body Gamma (graph1 InternalUnpair.right gd gm)))
    (hp : Nonempty (Derivation body Gamma
      (UniformCertificateCompletion.PositiveGuard.accepted BottomRepresentative.bottomTest
        BottomSpineMeasure.measure edge fp gp witness parameter))) :
    Nonempty (Derivation body Gamma
      (marked g gm gd ⊓ InternalOriginalOrderSyntaxProof.ltF gd fd)) := by
  have hfm := payloadMeasure f fp fm hfp (andLeft hf)
  have hfd := andRight (andRight hf)
  have hrawMarked := andIntro hfm (andIntro hgm (andIntro hfd hgd))
  have hc := PositiveSpineRulesProof.recover BottomRepresentative.bottomTest BottomSpineMeasure.measure
    edge fp gp witness parameter fm gm fd gd hrawMarked hp
  obtain ⟨hconditional⟩ := andRight (andRight hc)
  obtain ⟨hflag⟩ := andLeft (andRight hf)
  have hsuccessor : Nonempty (Derivation body Gamma
      (graph1 InternalUnpair.left InternalOriginalStepGuard.one gm ⊓
        InternalOriginalOrderSyntaxProof.ltF gd fd)) :=
    ⟨Derivation.implicationElimination hconditional hflag⟩
  exact andIntro
    (andIntro (objectMeasureValue g gp gm hgp hgm) (andIntro (andLeft hsuccessor) hgd))
    (andRight hsuccessor)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.GlobalSourceSpineMeasureProof
