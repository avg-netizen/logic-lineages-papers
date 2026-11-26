module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalArithmeticProgramsMultiplicationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalArithmeticPrograms
open ID1Completion.InternalArithmeticProgramsSupportProof (additionValue)
open ID1Completion.InternalArithmeticProgramsMultiplicationProof (multiplicationValue)
open ID1Completion.InternalControlGraphSupportProof
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn suc)
open ID1Completion.InternalTagArithmeticSupportProof (symm)
open NumberedWindowInternalSparsePair NumberedWindowInternalSparsePairTargets

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem squareGraph (x y : OTerm α) :
    Nonempty (Derivation body Γ (programGraph squaredSum
      (OrdinaryArithmetic.mulTerm (OrdinaryArithmetic.addTerm x y) (OrdinaryArithmetic.addTerm x y)) ![x,y])) := by
  let s := OrdinaryArithmetic.addTerm x y
  have h : Nonempty (Derivation body Γ (programGraph addition s ![x,y])) := additionValue x y
  apply compositionValue multiplication ![addition,addition] (OrdinaryArithmetic.mulTerm s s)
    ![x,y] ![s,s] (multiplicationValue s s)
  intro i
  exact Fin.cases h (Fin.cases h (fun k => Fin.elim0 k)) i

theorem pairGraph (x y : OTerm α) :
    Nonempty (Derivation body Γ (programGraph NumberedWindowInternalSparsePair.pair (pairTerm x y) ![x,y])) := by
  let s := OrdinaryArithmetic.addTerm x y
  let sq := OrdinaryArithmetic.mulTerm s s
  apply compositionValue addition ![squaredSum,.projection 0] (pairTerm x y) ![x,y] ![sq,x]
    (additionValue sq x)
  intro i
  exact Fin.cases (squareGraph x y) (Fin.cases (projectionValue (0 : Fin 2) ![x,y])
    (fun k => Fin.elim0 k)) i

theorem consGraph (x y : OTerm α) :
    Nonempty (Derivation body Γ (programGraph fieldCons (suc (pairTerm x y)) ![x,y])) := by
  apply compositionValue .succ (fun _ : Fin 1 => NumberedWindowInternalSparsePair.pair)
    (suc (pairTerm x y)) ![x,y] ![pairTerm x y] (successorValue ![pairTerm x y])
  intro i
  obtain rfl := Fin.eq_zero i
  exact pairGraph x y

theorem pairEquation (out x y : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph NumberedWindowInternalSparsePair.pair out ![x,y]))) :
    Nonempty (Derivation body Γ (eqn out (pairTerm x y))) :=
  valueUnique NumberedWindowInternalSparsePair.pair out (pairTerm x y) ![x,y] h (pairGraph x y)

theorem consEquation (out x y : OTerm α)
    (h : Nonempty (Derivation body Γ (programGraph fieldCons out ![x,y]))) :
    Nonempty (Derivation body Γ (eqn out (suc (pairTerm x y)))) :=
  valueUnique fieldCons out (suc (pairTerm x y)) ![x,y] h (consGraph x y)

theorem openPairGraph : OpenPairGraph := by
  intro body α out x y
  let G := programGraph NumberedWindowInternalSparsePair.pair out ![x,y]
  let E := eqn out (pairTerm x y)
  rw [equalEqn]
  obtain ⟨hf⟩ := pairEquation (body := body) (Γ := [G]) out x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := outputTransport (body := body) (Gamma := [E]) NumberedWindowInternalSparsePair.pair
    (pairTerm x y) out ![x,y] ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (pairGraph x y)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem openConsGraph : OpenFieldConsGraph := by
  intro body α out x y
  let G := programGraph fieldCons out ![x,y]
  let E := eqn out (suc (pairTerm x y))
  rw [equalEqn]
  obtain ⟨hf⟩ := consEquation (body := body) (Γ := [G]) out x y
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := outputTransport (body := body) (Gamma := [E]) fieldCons
    (suc (pairTerm x y)) out ![x,y] ⟨symm (Derivation.hypothesis List.mem_cons_self)⟩ (consGraph x y)
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairGraphProof
