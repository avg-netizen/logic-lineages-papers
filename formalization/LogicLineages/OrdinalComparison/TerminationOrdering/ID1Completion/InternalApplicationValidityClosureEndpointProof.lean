module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStructuralEndpointGuardSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationValidityStack InternalApplicationValidityClosure
open InternalApplicationValidityClosureEndpointSupportProof InternalStructuralEndpointGuardSupportProof
open InternalAcceptanceConjunctionProof InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- The endpoint supplies every raw tag, both source acceptances, target
acceptance and codomain membership. Only the two source acceptances are
split into target and universe branches; no universe condition is used on t. -/
theorem endpointApplicationValidity (old : InternalOriginalStepGuard.Data) (member : Program 1)
    (arrow d e s t a sourceApp targetApp : OTerm α)
    (h : Nonempty (Derivation body Gamma
      (endpointApplicationPremises old member arrow d e s t a sourceApp targetApp))) :
    Nonempty (Derivation body Gamma
      (graph1 (recursiveData old member).sourceValid (suc z) sourceApp ⊓
        graph1 (recursiveData old member).targetValid (suc z) targetApp)) := by
  let target := validator (InternalLessThan.constantOne 1) old.targetValid
  let universeValidator := validator member old.sourceValid
  have har := andLeft h
  have hr := endpointRecover (recursiveData old member) member arrow d e s t a
    har (andLeft (andRight h))
  have hs := conjunctionRecover target universeValidator (Fin.cons s Fin.elim0) (andLeft hr)
  have ht := andLeft (andRight hr)
  have ha := conjunctionRecover target universeValidator (Fin.cons a Fin.elim0)
    (andLeft (andRight (andRight hr)))
  have htail := andRight (andRight (andRight hr))
  have htags := andLeft htail
  have hm := andRight htail
  have hsl := andLeft htags
  have htl := andLeft (andRight htags)
  have hal := andRight (andRight htags)
  have hsapp := andLeft (andRight (andRight h))
  have htapp := andRight (andRight (andRight h))
  have hone : Nonempty (Derivation body Gamma
      (graph1 (InternalLessThan.constantOne 1) (suc z) e)) :=
    InternalLessThanSupportProof.oneConstantValue (Fin.cons e Fin.elim0)
  have hsourceTarget := rawApplicationClosure (InternalLessThan.constantOne 1)
    old.targetValid arrow d e s a sourceApp har hsl hal hone (andLeft hs) (andLeft ha) hsapp
  have hsourceUniverse := rawApplicationClosure member old.sourceValid
    arrow d e s a sourceApp har hsl hal hm (andRight hs) (andRight ha) hsapp
  have htarget := rawApplicationClosure (InternalLessThan.constantOne 1)
    old.targetValid arrow d e t a targetApp har htl hal hone ht (andLeft ha) htapp
  exact andIntro
    (conjunctionAccept target universeValidator (Fin.cons sourceApp Fin.elim0)
      hsourceTarget hsourceUniverse) htarget

theorem actualOriginalRecursiveEndpointApplicationValidity :
    InternalApplicationValidityClosureTargets.ActualOriginalRecursiveEndpointApplicationValidity := by
  intro body old member α arrow d e s t a sourceApp targetApp
  let premise := endpointApplicationPremises old member arrow d e s t a sourceApp targetApp
  obtain ⟨h⟩ := endpointApplicationValidity (body := body) (Gamma := [premise])
    old member arrow d e s t a sourceApp targetApp ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointProof
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityClosureEndpointProof
