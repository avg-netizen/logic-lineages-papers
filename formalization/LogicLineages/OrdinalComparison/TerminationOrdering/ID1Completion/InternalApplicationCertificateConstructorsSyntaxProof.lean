module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)

theorem positionTermEq {α : Type} : (positionTerm : OTerm α) = suc (suc z) := rfl

@[simp] theorem positionTermRename {α β : Type} (j : α → β) :
    (positionTerm : OTerm α).relabel j = positionTerm := by
  simp only [positionTermEq,sucRelabel,zRelabel]

@[simp] theorem graph1Rename {α β : Type} (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 1)
    (out x : OTerm α) (j : α → β) :
    (graph1 p out x).relabel j = graph1 p (out.relabel j) (x.relabel j) := by
  simp only [graph1,programRename,consTermRename,emptyRename]

@[simp] theorem graph2Rename {α β : Type} (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 2)
    (out x y : OTerm α) (j : α → β) :
    (graph2 p out x y).relabel j = graph2 p (out.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [graph2,programRename,consTermRename,emptyRename]

@[simp] theorem graph3Rename {α β : Type} (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3)
    (out x y z : OTerm α) (j : α → β) :
    (graph3 p out x y z).relabel j =
      graph3 p (out.relabel j) (x.relabel j) (y.relabel j) (z.relabel j) := by
  simp only [graph3,programRename,consTermRename,emptyRename]

@[simp] theorem graph4Rename {α β : Type} (p : LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 4)
    (out w x y z : OTerm α) (j : α → β) :
    (graph4 p out w x y z).relabel j =
      graph4 p (out.relabel j) (w.relabel j) (x.relabel j) (y.relabel j) (z.relabel j) := by
  simp only [graph4,programRename,consTermRename,emptyRename]

@[simp] theorem selectorsRename {α β : Type} (certificate s t k : OTerm α) (j : α → β) :
    (selectors certificate s t k).relabel j =
      selectors (certificate.relabel j) (s.relabel j) (t.relabel j) (k.relabel j) := by
  change (graph1 source s certificate).relabel j ⊓
    ((graph1 target t certificate).relabel j ⊓ (graph1 step k certificate).relabel j) = _
  rw [graph1Rename,graph1Rename,graph1Rename]
  rfl

@[simp] theorem liftPremisesRename {α β : Type}
    (d e a certificate s t k s' t' k' : OTerm α) (j : α → β) :
    (liftPremises d e a certificate s t k s' t' k').relabel j =
      liftPremises (d.relabel j) (e.relabel j) (a.relabel j) (certificate.relabel j)
        (s.relabel j) (t.relabel j) (k.relabel j) (s'.relabel j) (t'.relabel j) (k'.relabel j) := by
  change (graph3 edgeCode certificate s t k).relabel j ⊓
    ((graph4 application s' d e s a).relabel j ⊓
      ((graph4 application t' d e t a).relabel j ⊓ (graph1 stepLift k' k).relabel j)) = _
  rw [graph3Rename,graph4Rename,graph4Rename,graph1Rename]
  rfl

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
