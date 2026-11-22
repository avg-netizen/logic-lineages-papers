module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixTargets
import LogicLineages.PermittedControl.SignedCongruenceMatrixCodeStepProof
import LogicLineages.PermittedControl.SharedRankResidueRowStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrix
open PreparedProjection FiniteStripCollectorRecovery
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open MixedRankNamedResidueRow (RawArgs)
open SharedRankResidueRow (SourceRow Layout requests encodeRow commonLayout commonLayoutCode)
open RankResidueChoices (Slot)
open StatementChecks (fixed_sharedRankResidueRowCodeExact)

private theorem compilePrimitive : Primrec compileCode := by
  let Step := List RawArgs × (RawArgs × Option Nat)
  have layout : Primrec (fun p : Step => commonLayoutCode p.1) :=
    fixed_sharedRankResidueRowCodeExact.1.comp Primrec.fst
  have state : Primrec (Prod.snd : Step → RawArgs × Option Nat) := Primrec.snd
  have step := conjoinPrimitive.comp (layout.pair state)
  have folded := Primrec.list_foldr (Primrec.id : Primrec (id : List RawArgs → List RawArgs))
    (Primrec.const (some (0 : Nat))) step.to₂
  have slot : Primrec (fun s : Slot => ((s.1,(0,s.2,(0,0,0,0))) : NamedCode)) :=
    Primrec.fst.pair ((Primrec.const 0).pair (Primrec.snd.pair (Primrec.const (0,0,0,0))))
  have tape : Primrec (fun r : List RawArgs => (commonLayoutCode r).map
      (fun s => ((s.1,(0,s.2,(0,0,0,0))) : NamedCode))) :=
    Primrec.list_map fixed_sharedRankResidueRowCodeExact.1 (slot.comp Primrec.snd).to₂
  exact Primrec.option_map folded ((tape.comp Primrec.fst).pair Primrec.snd).to₂

private theorem foldNone (layout : Layout) (rows : List RawArgs) :
    rows.foldr (conjoinCode layout) (some 0) = none ↔ ∃ r ∈ rows, r.1 = 0 := by
  induction rows with
  | nil => simp
  | cons r tail ih =>
    rw [List.foldr_cons,conjoinNone,ih]
    constructor
    · rintro (zero | ⟨q,member,zero⟩)
      · exact ⟨r,List.mem_cons_self,zero⟩
      · exact ⟨q,List.mem_cons_of_mem _ member,zero⟩
    · rintro ⟨q,member,zero⟩
      rcases List.mem_cons.mp member with equal | later
      · subst q
        exact Or.inl zero
      · exact Or.inr ⟨q,later,zero⟩

private theorem foldLiteral (layout : Layout) (rows : List SourceRow)
    (positive : ∀ r ∈ rows, 0 < r.1) :
    (rows.map encodeRow).foldr (conjoinCode layout) (some 0) = some (formulaAtLayout layout rows).encode := by
  induction rows with
  | nil => rfl
  | cons r tail ih =>
    change conjoinCode layout (encodeRow r) ((tail.map encodeRow).foldr (conjoinCode layout) (some 0)) =
      some (.conjunction (SharedRankResidueRow.formula layout r) (formulaAtLayout layout tail) : NormalForm.Formula).encode
    rw [ih (fun q member => positive q (List.mem_cons_of_mem _ member))]
    simp [conjoinCode,fixed_sharedRankResidueRowCodeExact.2.2.2.2 layout r (positive r List.mem_cons_self),
      NormalForm.Formula.encode]

theorem codeExact : CodeExact := by
  refine ⟨compilePrimitive,?_,?_⟩
  · intro rows
    simp only [compileCode,Option.map_eq_none_iff,foldNone]
  · intro rows positive
    unfold compileCode formula
    rw [fixed_sharedRankResidueRowCodeExact.2.2.1,foldLiteral (commonLayout rows) rows positive]
    simp [requests,List.map_map,Function.comp_def,encodeRequest,LowerOperand.code]

end LogicLineages.PermittedControl.SignedCongruenceMatrix
