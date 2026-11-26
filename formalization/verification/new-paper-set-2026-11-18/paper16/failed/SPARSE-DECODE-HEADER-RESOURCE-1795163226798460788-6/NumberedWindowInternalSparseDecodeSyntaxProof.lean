module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (programRename emptyRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparseDecode (good leftCandidate rightCandidate)
open NumberedWindowInternalSparseDecodeTargets

abbrev unary {α : Type} (p : Program 1) (out x : OTerm α) : Formula α :=
  programGraph p out (Fin.cons x Fin.elim0)

abbrev binary {α : Type} (p : Program 2) (out x y : OTerm α) : Formula α :=
  programGraph p out (Fin.cons x (Fin.cons y Fin.elim0))

@[simp] theorem unaryRename {α β : Type} (p : Program 1) (out x : OTerm α) (j : α → β) :
    (unary p out x).relabel j = unary p (out.relabel j) (x.relabel j) := by
  simp only [unary,programRename,consTermRename,emptyRename]

@[simp] theorem binaryRename {α β : Type} (p : Program 2) (out x y : OTerm α) (j : α → β) :
    (binary p out x y).relabel j = binary p (out.relabel j) (x.relabel j) (y.relabel j) := by
  simp only [binary,programRename,consTermRename,emptyRename]

theorem certifiedRename {α β : Type} (n x y : OTerm α) (j : α → β) :
    (certifiedOutputs n x y).relabel j = certifiedOutputs (n.relabel j) (x.relabel j) (y.relabel j) := by
  change (unary good (suc z) n ⊓ (unary leftCandidate x n ⊓ unary rightCandidate y n)).relabel j =
    (unary good (suc z) (n.relabel j) ⊓
      (unary leftCandidate (x.relabel j) (n.relabel j) ⊓ unary rightCandidate (y.relabel j) (n.relabel j)))
  simp only [conjunctionRename,unaryRename,sucRelabel,zRelabel]

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
