module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram InternalListCodec
open InternalControlGraphSupportProof InternalRecursionClosureProof InternalRecursionClosureLogicProof
open InternalGraphCompositionFunctionalityProof InternalGraphCompositionSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalTagArithmeticSupportProof
open InternalSourceInversionSupportProof InternalPositiveUnfoldingSupportProof
open InternalEqualityTestPredecessorProof InternalBetaTotalityProof InternalAcceptanceSupportProof

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

abbrev unaryGraph (p : Program 1) (out n : OTerm α) : Formula α :=
  programGraph p out (Fin.cons n Fin.elim0)

abbrev consGraph (n h t : OTerm α) : Formula α :=
  programGraph consCode n (Fin.cons h (Fin.cons t Fin.elim0))

abbrev pairGraph (p h t : OTerm α) : Formula α :=
  programGraph InternalPairing.pairing p (Fin.cons h (Fin.cons t Fin.elim0))

def consResult (n h t : OTerm α) : Formula α :=
  (unaryGraph headCode h n) ⊓ ((unaryGraph tailCode t n) ⊓ (eqn n z).not)

@[simp] theorem unaryGraphRename {β : Type} (p : Program 1) (out n : OTerm α) (j : α → β) :
    (unaryGraph p out n).relabel j = unaryGraph p (out.relabel j) (n.relabel j) := by
  simp only [unaryGraph,programRename,consTermRename,emptyRename]

@[simp] theorem consGraphRename {β : Type} (n h t : OTerm α) (j : α → β) :
    (consGraph n h t).relabel j = consGraph (n.relabel j) (h.relabel j) (t.relabel j) := by
  simp only [consGraph,programRename,consTermRename,emptyRename]

@[simp] theorem consResultRename {β : Type} (n h t : OTerm α) (j : α → β) :
    (consResult n h t).relabel j = consResult (n.relabel j) (h.relabel j) (t.relabel j) := by
  change (unaryGraph headCode h n).relabel j ⊓
    ((unaryGraph tailCode t n).relabel j ⊓ ((eqn n z).relabel j).not) = _
  rw [unaryGraphRename,unaryGraphRename,eqnRelabel,zRelabel]
  rfl

theorem consValue (p h t : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph p h t))) :
    Nonempty (Derivation body Gamma (consGraph (suc p) h t)) := by
  apply compositionValue .succ (fun _ : Fin 1 => InternalPairing.pairing)
    (suc p) (Fin.cons h (Fin.cons t Fin.elim0)) (Fin.cons p Fin.elim0)
    (successorValue (Fin.cons p Fin.elim0))
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact hp

theorem headAfterPair (p h t : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph p h t))) :
    Nonempty (Derivation body Gamma (unaryGraph headCode h (suc p))) := by
  obtain ⟨hi⟩ := closedApply (InternalUnpairProof.actualOriginalGeneratedCodeInverse body α p h t) hp
  apply compositionValue InternalUnpair.left (fun _ : Fin 1 => InternalEqualityTest.predecessor)
    h (Fin.cons (suc p) Fin.elim0) (Fin.cons p Fin.elim0)
    ⟨Derivation.conjunctionLeft hi⟩
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact predecessorSuccessor p

theorem tailAfterPair (p h t : OTerm α)
    (hp : Nonempty (Derivation body Gamma (pairGraph p h t))) :
    Nonempty (Derivation body Gamma (unaryGraph tailCode t (suc p))) := by
  obtain ⟨hi⟩ := closedApply (InternalUnpairProof.actualOriginalGeneratedCodeInverse body α p h t) hp
  apply compositionValue InternalUnpair.right (fun _ : Fin 1 => InternalEqualityTest.predecessor)
    t (Fin.cons (suc p) Fin.elim0) (Fin.cons p Fin.elim0)
    ⟨Derivation.conjunctionRight hi⟩
  intro i
  obtain rfl : i = 0 := Fin.eq_zero i
  exact predecessorSuccessor p

/-- Destruction at a supplied pair witness uses only graph functionality and
predecessor-successor inversion in the original calculus. -/
theorem consAtPair (n p h t : OTerm α)
    (hn : Nonempty (Derivation body Gamma (consGraph n h t)))
    (hp : Nonempty (Derivation body Gamma (pairGraph p h t))) :
    Nonempty (Derivation body Gamma (consResult n h t)) := by
  obtain ⟨he⟩ := valueUnique consCode n (suc p)
    (Fin.cons h (Fin.cons t Fin.elim0)) hn (consValue p h t hp)
  obtain ⟨hh⟩ := headTransport headCode h (suc p) n Fin.elim0
    ⟨symm he⟩ (headAfterPair p h t hp)
  obtain ⟨ht⟩ := headTransport tailCode t (suc p) n Fin.elim0
    ⟨symm he⟩ (tailAfterPair p h t hp)
  have hz : Derivation body Gamma (eqn n z).not :=
    Derivation.implicationIntroduction (sucNeZeroApply
      (trans (symm (addHyp he _)) (Derivation.hypothesis List.mem_cons_self)))
  exact ⟨Derivation.conjunctionIntroduction hh (Derivation.conjunctionIntroduction ht hz)⟩

/-- The witness comes from proved original pairing totality, and is eliminated
by the original existential rule. No semantic evaluation enters the argument. -/
theorem consDestruction (n h t : OTerm α)
    (hn : Nonempty (Derivation body Gamma (consGraph n h t))) :
    Nonempty (Derivation body Gamma (consResult n h t)) := by
  apply programCases InternalPairing.pairing (Fin.cons h (Fin.cons t Fin.elim0)) _
  intro β j Delta p hj hp
  rw [consResultRename]
  simp only [consTermRename,emptyRename] at hp
  have hn' := renameInto hn j Delta hj
  rw [consGraphRename] at hn'
  exact consAtPair (n.relabel j) p (h.relabel j) (t.relabel j) hn' hp

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
