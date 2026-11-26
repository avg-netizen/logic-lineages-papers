module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationTargets
public import LogicLineages.OrdinalComparison.ScalarAnnotationDataStructureProof
public import LogicLineages.StandardControlCurrent.PolicyShapeSyntaxProof
public import Mathlib.Tactic.FinCases
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum ScalarAnnotationData ActiveScalarAnnotation AdditiveHeadTree

theorem validTree : CurrentGroundAnnotationTargets.ValidTree := by
  intro p k Γ F d hd
  induction d with
  | free q => exact ⟨.free hd.1 hd.2,.free hd.2⟩
  | tracked => exact ⟨.tracked,.tracked⟩
  | add a b iha ihb =>
    have ha := iha hd.1
    have hb := ihb hd.2
    exact ⟨.add ha.1 hb.1,.add ha.2 hb.2⟩
  | collapse op tail ih =>
    have ht := ih hd.2.2.2
    have hop : GroundOperatorDischarge.OperatorWitness p op.head :=
      ⟨op.arity,op.source,op.vector,hd.1,rfl⟩
    exact ⟨.collapse hd.2.1 ht.1,.collapse hop hd.2.2.1 ht.2⟩

theorem oneValid (p : Policy) {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))} :
    Valid p (Tree.free (k := k) (F := F) .one) :=
  ⟨GeneratedOrdinalGrade.one 0,by simp [Active]⟩

theorem closeOperatorAssignment (p : Policy) {Γ} (op : Operator (.ground :: Γ))
    (hop : AdmissibleAssignment.assignment p op.source = some op.vector) :
    AdmissibleAssignment.assignment p (closeOperator op).source =
      some (closeOperator op).vector := by
  change AdmissibleAssignment.assignment p (GroundOperatorDischarge.close op.source) =
    some (fun j => ordinalHeadClosure (op.vector j))
  rw [GroundOperatorDischarge.Proof.wholeAssignment,hop]
  rfl

theorem closeValid (p : Policy) {k Γ} {F : Variable Γ (Ty.curriedGround (k+1))}
    (d : Tree k (.ground :: Γ) (.there F)) (hd : Valid p d) : Valid p (closeTree d) := by
  induction d with
  | free q =>
    exact ⟨actualGeneratedGradeHeadClosure Γ .ground 0 q hd.1,
      fun ha => hd.2 ((ActiveScalarAnnotation.Proof.active_headClosure F q).1 ha)⟩
  | tracked => trivial
  | add a b iha ihb => exact ⟨iha hd.1,ihb hd.2⟩
  | collapse op tail ih =>
    refine ⟨closeOperatorAssignment p op hd.1,
      AdditiveHeadTree.Proof.headClosureHead k Γ F op.head hd.2.1,?_,ih hd.2.2.2⟩
    intro ha
    have hhead := (ActiveScalarAnnotation.Proof.active_headClosure F op.head).1 ha
    have htail := hd.2.2.1 hhead
    rw [ScalarAnnotationData.Proof.close_erase]
    exact (ActiveScalarAnnotation.Proof.active_headClosure F (erase tail)).2 htail

theorem expandErase {k Γ F n} (s : Shape n) (xs : Fin n → Tree k Γ F) :
    erase (expandTree s xs) = expand s (fun i => erase (xs i)) := by
  induction s with
  | leaf => rfl
  | @join n m a b iha ihb =>
    change (.add (erase (expandTree a (fun i => xs (Fin.castAdd m i))))
      (erase (expandTree b (fun i => xs (Fin.natAdd n i)))) : OrdinalExpression Γ) =
      .add (expand a (fun i => erase (xs (Fin.castAdd m i))))
        (expand b (fun i => erase (xs (Fin.natAdd n i))))
    rw [iha,ihb]

theorem expandValid (p : Policy) {k Γ F n} (s : Shape n) (xs : Fin n → Tree k Γ F)
    (hxs : ∀ j, Valid p (xs j)) : Valid p (expandTree s xs) := by
  induction s with
  | leaf => exact hxs 0
  | @join n m a b iha ihb =>
    exact ⟨iha (fun i => xs (Fin.castAdd m i)) (fun i => hxs (Fin.castAdd m i)),
      ihb (fun i => xs (Fin.natAdd n i)) (fun i => hxs (Fin.natAdd n i))⟩

theorem repeatErase (p : Policy) {k Γ F} (d : Tree k Γ F) (n : Nat) :
    erase (repeatTree p d n) = AdmissibleAssignment.repeated p .scalarRepeat n (erase d) := by
  cases n with
  | zero => rfl
  | succ n => exact expandErase (p.shape .scalarRepeat n) _

theorem repeatValid (p : Policy) {k Γ F} (d : Tree k Γ F) (n : Nat)
    (hn : 0 < n) (hd : Valid p d) : Valid p (repeatTree p d n) := by
  cases n with
  | zero => omega
  | succ n => exact expandValid p (p.shape .scalarRepeat n) _ (fun _ => hd)

theorem threeErase (p : Policy) {k Γ F} (a b : Tree k Γ F) :
    erase (threeTree p a b) = AdmissiblePartial.three p .activeAdd (erase a) (erase b) .one := by
  unfold threeTree AdmissiblePartial.three
  rw [expandErase]
  apply congrArg (expand (p.shape .activeAdd 2))
  funext i
  fin_cases i <;> rfl

theorem threeValid (p : Policy) {k Γ F} (a b : Tree k Γ F)
    (ha : Valid p a) (hb : Valid p b) : Valid p (threeTree p a b) := by
  apply expandValid
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact oneValid p

theorem markerFramed (k : Nat) (Γ : List Ty) (F : Variable Γ (Ty.curriedGround (k+1)))
    (n : Nat) (s : Shape n) (xs : Fin n → Tree k Γ F) (rest stack : List Nat) :
    CurrentGroundAnnotationCode.run (PolicyShape.shapeCode s)
      (some (List.ofFn (fun j => SourceAnnotationCode.code (xs j)) ++ rest,stack)) =
      some (rest,SourceAnnotationCode.code (expandTree s xs)::stack) := by
  induction s generalizing rest stack with
  | leaf => simp [PolicyShape.shapeCode,CurrentGroundAnnotationCode.run,
      CurrentGroundAnnotationCode.markStep,expandTree,List.ofFn_succ]
  | @join n m a b iha ihb =>
    have hl := iha (fun i => xs (Fin.castAdd m i))
      (List.ofFn (fun i => SourceAnnotationCode.code (xs (Fin.natAdd n i))) ++ rest) stack
    have hr := ihb (fun i => xs (Fin.natAdd n i)) rest
      (SourceAnnotationCode.code (expandTree a (fun i => xs (Fin.castAdd m i)))::stack)
    simp only [PolicyShape.shapeCode,CurrentGroundAnnotationCode.run,List.foldl_append]
    rw [List.ofFn_add,List.append_assoc]
    change CurrentGroundAnnotationCode.run [true]
      (CurrentGroundAnnotationCode.run (PolicyShape.shapeCode b)
        (CurrentGroundAnnotationCode.run (PolicyShape.shapeCode a)
          (some (List.ofFn (fun i => SourceAnnotationCode.code (xs (Fin.castAdd m i))) ++
            (List.ofFn (fun i => SourceAnnotationCode.code (xs (Fin.natAdd n i))) ++ rest),stack)))) = _
    rw [hl,hr]
    simp [CurrentGroundAnnotationCode.run,CurrentGroundAnnotationCode.markStep,expandTree,SourceAnnotationCode.code]

theorem markerMacro (p : Policy) (site : MacroSite) {k Γ F} (n : Nat)
    (xs : Fin (n+1) → Tree k Γ F) :
    CurrentGroundAnnotationCode.macroCode p (PolicyShape.siteCode site) n
      (List.ofFn (fun j => SourceAnnotationCode.code (xs j))) =
      some (SourceAnnotationCode.code (expandTree (p.shape site n) xs)) := by
  unfold CurrentGroundAnnotationCode.macroCode PolicyShape.selector
  rw [PolicyShapeSyntaxProof.sites]
  have h := markerFramed k Γ F (n+1) (p.shape site n) xs [] []
  rw [List.append_nil] at h
  rw [h]
  rfl

theorem markerExpansion : CurrentGroundAnnotationTargets.MarkerExpansion := by
  refine ⟨markerFramed,?_⟩
  intro k Γ F p n d
  cases n with
  | zero => rfl
  | succ n =>
    simpa only [CurrentGroundAnnotationCode.repeatCode,Nat.add_one_ne_zero,if_false,
      Nat.add_sub_cancel,repeatTree,List.ofFn_const] using
      markerMacro p .scalarRepeat n (fun _ => d)

theorem markerThree (p : Policy) {k Γ F} (a b : Tree k Γ F) :
    CurrentGroundAnnotationCode.macroCode p (PolicyShape.siteCode .activeAdd) 2
      [SourceAnnotationCode.code a,SourceAnnotationCode.code b,4] =
      some (SourceAnnotationCode.code (threeTree p a b)) := by
  have he := markerMacro p .activeAdd 2
    (Fin.cases a (Fin.cases b (fun _ => Tree.free .one)))
  change CurrentGroundAnnotationCode.macroCode p (PolicyShape.siteCode .activeAdd) 2
    [SourceAnnotationCode.code a,SourceAnnotationCode.code b,4] =
      some (SourceAnnotationCode.code (threeTree p a b)) at he
  exact he

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotation
