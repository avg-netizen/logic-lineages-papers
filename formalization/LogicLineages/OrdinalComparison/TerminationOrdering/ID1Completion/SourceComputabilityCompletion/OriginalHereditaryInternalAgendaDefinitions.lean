module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAgendaPotentialDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgenda
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open InternalTagArithmeticSyntaxProof (suc)
open InternalOriginalOrderSyntaxProof (ltF)
open InternalClosedPrograms (allBlock)
open InternalFiniteBlocks (block)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Eight actual coordinates: role,type,typed payload,raw job,raw,parameter,Gamma,weight.
The original window c and global branching B remain fixed across every job. -/
def jobFields {alpha : Type} (H : Program 1) (M W : Program 2)
 (c B job role typ typed rawJob raw parameter gamma weight : OTerm alpha) : Formula alpha :=
 graph2 InternalPairing.pairing job role typed ⊓
 (graph2 InternalPairing.pairing typed typ rawJob ⊓
 (graph2 InternalPairing.pairing rawJob raw parameter ⊓
 (graph2 InternalPairing.pairing parameter c gamma ⊓
 (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c ⊓
 (graph1 OriginalHereditaryFuelProgram.weight weight job ⊓ ltF (suc (suc weight)) (suc B))))))
def jobMatrix {alpha : Type} (H : Program 1) (M W : Program 2) (c B job : OTerm alpha) : Formula (alpha ⊕ Fin 8) :=
 jobFields H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (job.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3))
  (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
def Job {alpha : Type} (H : Program 1) (M W : Program 2) (c B job : OTerm alpha) : Formula alpha :=
 block (jobMatrix H M W c B job)
/-- Both supported frame tags retain one and the same genuinely admissible job.
Return counts remain literal operational metadata; semantic result claims are separate. -/
def frameFields {alpha : Type} (H : Program 1) (M W : Program 2)
 (c B frame parent payload counts : OTerm alpha) : Formula alpha :=
 (graph2 InternalPairing.pairing frame (numeral 0) parent ⊔
  (graph2 InternalPairing.pairing frame (numeral 1) payload ⊓ graph2 InternalPairing.pairing payload parent counts)) ⊓
 Job H M W c B parent
def frameMatrix {alpha : Type} (H : Program 1) (M W : Program 2) (c B frame : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 frameFields H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (frame.relabel Sum.inl)
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
def Frame {alpha : Type} (H : Program 1) (M W : Program 2) (c B frame : OTerm alpha) : Formula alpha :=
 block (frameMatrix H M W c B frame)
def lookupFields {alpha : Type} (work count index frame : OTerm alpha) : Formula alpha :=
 graph1 OriginalContextInsertion.length count work ⊓
 (OriginalContextInsertion.Below index count ⊓ graph2 InternalRawListRecursion.lookup frame index work)
def agendaMatrix {alpha : Type} (H : Program 1) (M W : Program 2) (c B work : OTerm alpha) : Formula (alpha ⊕ Fin 3) :=
 (lookupFields (work.relabel Sum.inl) (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))).imp
 (Frame H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr 2)))
/-- Genuine internal bounded lookup invariant, not a Lean-level universal and
not the native AgendaTyped predicate. Results are deliberately not constrained. -/
def Agenda {alpha : Type} (H : Program 1) (M W : Program 2) (c B work : OTerm alpha) : Formula alpha :=
 allBlock (agendaMatrix H M W c B work)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgenda
