module
public import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectControlProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchControlChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenCellProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTapeProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators SourceComputabilityFormulaSupportProof
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue equalEqn)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open ID1Completion.InternalEqualityTest (equalityTest)
open ID1Completion.InternalEqualityTestProof (equalityOfAcceptance)
open ID1Completion.InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalProbeTargets (OTerm)
open NumberedWindowInternalFreshProbeDispatchProgram (compareNumbers bothOne)
open NumberedWindowInternalFreshProbeDispatchControlChecks (exact_DispatchControlAST)
open NumberedWindowInternalFreshProbeEmitterObjectTargets (consTerm)
open NumberedWindowInternalFreshProbeParsedEmitter (rawContext rawResult rawLeast arrowGood rawDomain rawCodomain)
open NumberedWindowInternalFreshProbeParsedEmitterObjectTargets (addressTerm addressReports)
open NumberedWindowInternalSparseFieldCell (cellGood cellHead cellTail)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (takeUnary)
open NumberedWindowInternalSparsePathEnvelopeOpenCellProof (cellEquation)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalAtomicApplicationShape NumberedWindowInternalAtomicApplicationShapeObjectTargets
open NumberedWindowInternalAtomicApplicationShapeObjectEmitterProof (addressGraph auxGraph)
open NumberedWindowInternalAtomicApplicationShapeObjectControlProof (callSlot)
open NumberedWindowInternalAtomicApplicationShapeObjectSyntaxProof (shapeIntro)

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

section
attribute [local irreducible] programGraph

private theorem takeSlot (p : Program 1) (i : Fin 3) (v : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (.composition p (fun _ : Fin 1 => .projection i)) v xs))) :
    Nonempty (Derivation B Γ (programGraph p v ![xs i])) := by
  apply compositionRecover p (fun _ : Fin 1 => .projection i) v xs ![xs i] h
  intro j
  obtain rfl := Fin.eq_zero j
  exact projectionValue i xs

private theorem checkedEq (p : Program 3) (i : Fin 3) (x : OTerm α) (xs : Fin 3 → OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph
      (.composition compareNumbers (Fin.cons (.projection i) (Fin.cons p Fin.elim0))) (suc z) xs)))
    (value : Nonempty (Derivation B Γ (programGraph p x xs))) :
    Nonempty (Derivation B Γ (equal (xs i) x)) := by
  let ps : Fin 2 → Program 3 := Fin.cons (.projection i) (Fin.cons p Fin.elim0)
  have actual := compositionRecover compareNumbers ps (suc z) xs ![xs i,x] h
    (fun j => Fin.cases (projectionValue i xs) (Fin.cases value (fun k => Fin.elim0 k)) j)
  rw [exact_DispatchControlAST.2.2.2.1] at actual
  rw [equalEqn]
  exact equalityOfAcceptance (xs i) x actual

private theorem argumentValue (f u y c d a : OTerm α)
    (hc : Nonempty (Derivation B Γ (programGraph rawContext c ![f])))
    (hd : Nonempty (Derivation B Γ (programGraph (atSource rawDomain) d ![f,u,y])))
    (ha : Nonempty (Derivation B Γ (programGraph (fromArgument rawLeast) a ![f,u,y]))) :
    Nonempty (Derivation B Γ (programGraph rebuildArgument (addressTerm c d a) ![f,u,y])) := by
  let xs : Fin 3 → OTerm α := ![f,u,y]
  let parts : Fin 3 → Program 3 := Fin.cons (atSource rawContext) (Fin.cons (atSource rawDomain)
    (Fin.cons (fromArgument rawLeast) Fin.elim0))
  change Nonempty (Derivation B Γ (programGraph (.composition addressEmitter parts) (addressTerm c d a) xs))
  apply compositionValue addressEmitter parts (addressTerm c d a) xs ![c,d,a] (addressGraph c d a)
  intro i
  have h₀ : Nonempty (Derivation B Γ (programGraph (atSource rawContext) c xs)) :=
    callSlot rawContext 0 c xs hc
  exact Fin.cases h₀ (Fin.cases hd (Fin.cases ha (fun k => Fin.elim0 k))) i

private theorem outputValue (f u y c d e k a' : OTerm α)
    (hc : Nonempty (Derivation B Γ (programGraph rawContext c ![f])))
    (hd : Nonempty (Derivation B Γ (programGraph (atSource rawDomain) d ![f,u,y])))
    (he : Nonempty (Derivation B Γ (programGraph (atSource rawCodomain) e ![f,u,y])))
    (hk : Nonempty (Derivation B Γ (programGraph rawLeast k ![f])))
    (ha : Nonempty (Derivation B Γ (programGraph (atTarget auxArgument) a' ![f,u,y]))) :
    Nonempty (Derivation B Γ (programGraph rebuildResult (auxAddressTerm c d e k a') ![f,u,y])) := by
  let xs : Fin 3 → OTerm α := ![f,u,y]
  let parts : Fin 5 → Program 3 := Fin.cons (atSource rawContext) (Fin.cons (atSource rawDomain) (Fin.cons (atSource rawCodomain)
      (Fin.cons (atSource rawLeast) (Fin.cons (atTarget auxArgument) Fin.elim0))))
  change Nonempty (Derivation B Γ (programGraph (.composition auxAddressEmitter parts) (auxAddressTerm c d e k a') xs))
  apply compositionValue auxAddressEmitter parts (auxAddressTerm c d e k a') xs ![c,d,e,k,a'] (auxGraph c d e k a')
  intro i
  have h₀ : Nonempty (Derivation B Γ (programGraph (atSource rawContext) c xs)) :=
    callSlot rawContext 0 c xs hc
  have h₃ : Nonempty (Derivation B Γ (programGraph (atSource rawLeast) k xs)) :=
    callSlot rawLeast 0 k xs hk
  exact Fin.cases h₀ (Fin.cases hd (Fin.cases he (Fin.cases h₃ (Fin.cases ha (fun k => Fin.elim0 k))))) i

/-- Actual graph programs on one unchanged 3-slot tape. The four
outputs are kept as object terms, not selected by native evaluation. -/
@[expose] def fields : Fin 4 → Program 3 :=
  Fin.cons (atSource rawDomain) (Fin.cons (atSource rawCodomain)
    (Fin.cons (fromArgument rawLeast) (Fin.cons (atTarget auxArgument) Fin.elim0)))

theorem fromReports (f u y c t k : OTerm α) (ys : Fin 4 → OTerm α)
    (raw : Nonempty (Derivation B Γ (addressReports f c t k)))
    (checked : Nonempty (Derivation B Γ (programGraph atomicChecks (suc z) ![f,u,y])))
    (reports : ∀ i, Nonempty (Derivation B Γ (programGraph (fields i) (ys i) ![f,u,y]))) :
    Nonempty (Derivation B Γ (literalApplicationShape c t k u y)) := by
  let xs : Fin 3 → OTerm α := ![f,u,y]
  let d := ys 0
  let e := ys 1
  let a := ys 2
  let a' := ys 3
  have checked' := checked
  rw [atomicChecks, exact_DispatchControlAST.2.2.2.2.2] at checked'
  obtain ⟨ok⟩ := conjunctionRecover (atSource arrowGood) (bothOne sameArgument sameResult) xs checked'
  have rest : Nonempty (Derivation B Γ (programGraph (bothOne sameArgument sameResult) (suc z) xs)) :=
    ⟨Derivation.conjunctionRight ok⟩
  rw [exact_DispatchControlAST.2.2.2.2.2] at rest
  obtain ⟨pair⟩ := conjunctionRecover sameArgument sameResult xs rest
  obtain ⟨addr⟩ := raw
  have hc : Nonempty (Derivation B Γ (programGraph rawContext c ![f])) :=
    ⟨Derivation.conjunctionLeft addr⟩
  have ht : Nonempty (Derivation B Γ (programGraph rawResult t ![f])) :=
    ⟨Derivation.conjunctionLeft (Derivation.conjunctionRight addr)⟩
  have hk : Nonempty (Derivation B Γ (programGraph rawLeast k ![f])) :=
    ⟨Derivation.conjunctionRight (Derivation.conjunctionRight addr)⟩
  have flag : Nonempty (Derivation B Γ (programGraph arrowGood (suc z) ![f])) :=
    takeSlot arrowGood 0 (suc z) xs ⟨Derivation.conjunctionLeft ok⟩
  have gd : Nonempty (Derivation B Γ (programGraph (atSource rawDomain) d xs)) := reports 0
  have ge : Nonempty (Derivation B Γ (programGraph (atSource rawCodomain) e xs)) := reports 1
  have ga : Nonempty (Derivation B Γ (programGraph (fromArgument rawLeast) a xs)) := reports 2
  have ga' : Nonempty (Derivation B Γ (programGraph (atTarget auxArgument) a' xs)) := reports 3
  have hd : Nonempty (Derivation B Γ (programGraph rawDomain d ![f])) := takeSlot rawDomain 0 d xs gd
  have he : Nonempty (Derivation B Γ (programGraph rawCodomain e ![f])) := takeSlot rawCodomain 0 e xs ge
  have arg : Nonempty (Derivation B Γ (equal u (addressTerm c d a))) :=
    checkedEq rebuildArgument 1 (addressTerm c d a) xs ⟨Derivation.conjunctionLeft pair⟩
      (argumentValue f u y c d a hc gd ga)
  have out : Nonempty (Derivation B Γ (equal y (auxAddressTerm c d e k a'))) :=
    checkedEq rebuildResult 2 (auxAddressTerm c d e k a') xs ⟨Derivation.conjunctionRight pair⟩
      (outputValue f u y c d e k a' hc gd ge hk ga')
  have arr : Nonempty (Derivation B Γ (equal t (consTerm d e))) := by
    rw [equalEqn]
    exact cellEquation t d e (takeUnary cellGood rawResult (suc z) f t flag ht)
      (takeUnary cellHead rawResult d f t hd ht) (takeUnary cellTail rawResult e f t he ht)
  exact shapeIntro c t k u y ys arr arg out

end

end LogicLineages.PersistentMarking.NumberedWindowInternalAtomicApplicationShapeObjectTapeProof
