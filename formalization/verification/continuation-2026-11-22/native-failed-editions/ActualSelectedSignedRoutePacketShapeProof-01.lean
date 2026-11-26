module
public import LogicLineages.PermittedControl.ActualSelectedSignedRoutePacketTargets
import LogicLineages.PermittedControl.ActualBoundedSignedRoutesProof
import LogicLineages.PermittedControl.ActualFullLabelPairGuardsLowerProof
import LogicLineages.PermittedControl.ActualPreparedSlotAppendProof
import LogicLineages.PermittedControl.HighFieldPreparedPacketShapeProof
import LogicLineages.PermittedControl.StableSortedHighFieldPacketProof
import LogicLineages.PermittedControl.OriginalMatrixLinearRowFormulaShapeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
open OrdinalComparison FieldComparison PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open ActualPreparedSlotAppend (Packet exactPreparedAppend)
open ActualSignedOrdinaryPairHigh (OrderTest orientedPacket strictPacket equalPacket)
open ActualBoundedSignedRoutes (Tip Route routes exactTypedRouteLayout linearRoute signedRoute prefixGuard)
open ActualFiniteSignedNodeBranch (nodePacket)
open ActualFullLabelPairGuards (Pair Answer lowerShape)
open MixedSameRankResidue (WeightedOperand)
open ActualSymbolicZeroSuccessor (SyntaxState)
open OriginalMatrixLinearRowFormula (safeTruth safeFalsity safeTest safePolarity)
open StableSortedHighField (basePacket basePacketExact appendOrderShape)

private theorem strictShape (F G : ValueField) (lo : Nat) (c : Int) (k : OrderTest) (pos : Bool) :
    Shape (strictPacket F G lo c k pos) := by
  let base := basePacket F G lo (ActualSignedOrdinaryPairHigh.request k c).1
  have ready : PreparedInput base.1 base.2 :=
    (basePacketExact F G lo (lo+1) _ (Nat.lt_succ_self lo)).2
  exact appendOrderShape base.1 _ lo (safePolarity _ _ ready _)

private theorem orientedShape (F G : ValueField) (i j : Nat) (c : Int) (k : OrderTest) (pos : Bool) :
    Shape (orientedPacket F G i j c k pos) := by
  unfold orientedPacket
  split
  · exact strictShape _ _ _ _ _ _
  · split
    · exact strictShape _ _ _ _ _ _
    · change PreparedInput [] (OriginalMatrixLinearRowFormula.choosePolarity _ _)
      exact safePolarity _ _ (HighFieldPreparedPacket.packetShape.2.1 _ _ _) _

private theorem pairShape (top : Nat) (p : Pair) (a : Answer) :
    Shape (ActualFullLabelPairGuards.packet top p a) := by
  unfold ActualFullLabelPairGuards.packet
  split
  · exact lowerShape _ _
  · exact orientedShape _ _ _ _ _ _ _

private theorem compileShape (top : Nat) (ps : List Pair) (as : List Answer) :
    Shape (ActualFiniteFullValueGuards.compile top ps as) := by
  induction ps generalizing as with
  | nil =>
    cases as with
    | nil => exact safeTruth []
    | cons a as => exact safeFalsity []
  | cons p ps ih =>
    cases as with
    | nil => exact safeFalsity []
    | cons a as =>
      exact (exactPreparedAppend _ _ (pairShape top p a) (ih as)).1

private theorem guardShape (terms : List WeightedOperand) (top : Nat) (a : List Answer) :
    Shape (nodePacket terms top a) := compileShape _ _ _

private theorem namesShape (n : Nat) (xs : List WeightedOperand) :
    ∀ t ∈ ActualSyntaxLinearTerminal.names n xs,
      ∃ i : Nat, t.2 = .variable i ∧ i < n+xs.length := by
  induction xs generalizing n with
  | nil => intro t used; cases used
  | cons x xs ih =>
    intro t used
    rcases List.mem_cons.mp used with first | rest
    · subst t
      exact ⟨n,rfl,by simp only [List.length_cons]; omega⟩
    · obtain ⟨i,eq,bound⟩ := ih (n+1) t rest
      exact ⟨i,eq,by simp only [List.length_cons]; omega⟩

private theorem linearPacketShape (top : Nat) (test : OrderTest) (pos : Bool) (s : SyntaxState) :
    Shape (terminalPacket test pos (linearRoute top test pos s).tip) := by
  let terms := ActualRankedNormalizationSyntax.normalizedTerms s.terms
  let low := ActualSyntaxLinearTerminal.lower top terms
  let ops := low.map Prod.snd
  let row := ActualSyntaxLinearTerminal.termsRow top s.constant terms
  have plain : PlainPreparedRow row := by
    intro t used
    rcases List.mem_cons.mp used with first | rest
    · subst t
      exact ⟨0,rfl⟩
    · obtain ⟨i,eq,_⟩ := namesShape 1 low t rest
      exact ⟨i,eq⟩
  have bounds : ∀ n ∈ NormalForm.rowVariables row, n ≤ ops.length := by
    intro n used
    obtain ⟨t,member,rfl⟩ := List.mem_map.mp used
    rcases List.mem_cons.mp member with first | rest
    · subst t
      exact Nat.zero_le _
    · obtain ⟨i,eq,bound⟩ := namesShape 1 low t rest
      change t.2.name ≤ ops.length
      rw [eq]
      change i ≤ ops.length
      simpa only [ops,List.length_map,Nat.add_comm 1,Nat.lt_succ_iff] using bound
  exact safePolarity ops _ (safeTest ops test.test row plain bounds) pos

private theorem signedPacketShape (test : OrderTest) (pos : Bool) (coef : Int) :
    Shape (terminalPacket test pos (.signed coef)) := by
  change PreparedInput [] (if (if pos then signedBit test coef else !(signedBit test coef))
    then .truth else .falsity)
  split
  · exact safeTruth []
  · exact safeFalsity []

theorem exactEmittedRouteShape : ExactEmittedRouteShape := by
  intro top fuel
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro test positive s path member
    rcases (exactTypedRouteLayout top fuel test positive s path).mp member with idle | active
    · obtain ⟨_,rfl⟩ := idle
      exact ⟨fun p used => False.elim (List.not_mem_nil used),linearPacketShape top test positive s⟩
    · obtain ⟨_,a,_,br⟩ := active
      rcases br with tip | more
      · obtain ⟨_,rfl⟩ := tip
        refine ⟨?_,signedPacketShape _ _ _⟩
        intro p used
        have eq := List.mem_singleton.mp used
        rw [eq]
        exact guardShape s.terms top a
      · obtain ⟨_,k,out,depth,_,tail,htail,rfl⟩ := more
        have lt : k < fuel := by omega
        obtain ⟨shapeGuard,shapeTip⟩ := ih k lt test positive out tail htail
        refine ⟨?_,shapeTip⟩
        intro p used
        rcases List.mem_cons.mp used with first | rest
        · rw [first]
          exact guardShape s.terms top a
        · exact shapeGuard p rest

end LogicLineages.PermittedControl.ActualSelectedSignedRoutePacket
