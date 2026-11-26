module
public import LogicLineages.PermittedControl.GroundScalarCircuitTargets
import LogicLineages.PermittedControl.GroundScalarCircuitShapeProof
import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseStatementChecks
import LogicLineages.OrdinalComparison.RawNotationCode
import LogicLineages.OrdinalComparison.NaturalProductInterpretation

public section
namespace LogicLineages.PermittedControl.GroundScalarCircuit
open OrdinalComparison
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open OrdinalComparison.Source.ForwardTranslation (Scalar scalarHeadNote scalarCode fixedHead ClosedPositive)
open OriginalPrintedCircuitSequential (Gate Topological run baseResult)
open OriginalPrintedTypedExistential (HasSuccessfulObservation)
open OriginalPrintedCircuitTerminal (observe)
open SelectedGeneratedSource (scalarValueWith)

theorem headRepr (c : ClosedPositive) : (scalarHeadNote c).1.repr = fixedHead c := by
  rw [scalarHeadNote,naturalProductDenotation]
  simp [fixedHead,ONote.repr]

theorem collapseRead (f : Nat → Nat) (K : Nat) (hf : SelectedWithThreshold f K) (h : NONote) (u : Nat) :
    ArbitraryFixedHeadCollapse.read f (rawNoteEncode h.1,u) =
      some (ParametricActualCollapse.collapseWith f (h.1.repr + (u : Ordinal))) := by
  have hg := StatementChecks.fixed_arbitraryFixedHeadActualGraph f K hf (rawNoteEncode h.1,u)
  have dec : rawNoteDecode (rawNoteEncode h.1) = h.1 := rawNoteDecodeEncode h.1
  have key : ArbitraryFixedHeadCollapse.read f (rawNoteEncode h.1,u) =
      some (ParametricActualCollapse.collapseWith f ((rawNoteDecode (rawNoteEncode h.1)).repr + (u : Ordinal))) :=
    (hg.2 _).mpr ⟨by show ONote.NF (rawNoteDecode (rawNoteEncode h.1)); rw [dec]; exact h.2,rfl⟩
  rw [dec] at key
  exact key

theorem readAffine (f θ : Nat → Nat) (e : NaturalAffineGateGraph.Expression) (n v : Nat)
    (h : NaturalAffineGateGraph.signedValue e θ = (v : Int)) :
    (Gate.base (.affine e n)).read f θ = .ok v := by
  show baseResult (if 0 ≤ NaturalAffineGateGraph.signedValue e θ then
    some (NaturalAffineGateGraph.signedValue e θ).toNat else none) = .ok v
  rw [h,if_pos (Int.natCast_nonneg v)]
  simp [baseResult]

theorem readCollapse (f : Nat → Nat) (K : Nat) (hf : SelectedWithThreshold f K) (h : NONote)
    (src out : Nat) (θ : Nat → Nat) :
    (Gate.base (.collapse ⟨h,src,out⟩)).read f θ =
      .ok (ParametricActualCollapse.collapseWith f (h.1.repr + (θ src : Ordinal))) := by
  show baseResult (ArbitraryFixedHeadCollapse.read f (rawNoteEncode h.1,θ src)) = _
  rw [collapseRead f K hf h (θ src)]
  rfl

theorem singleRun (f θ : Nat → Nat) (g : Gate) (v : Nat) (h : g.read f θ = .ok v) :
    run f θ [g] = .ok (Function.update θ g.output v) := by
  simp only [run,h]

theorem runAppend (f : Nat → Nat) : ∀ (gs gs' : List Gate) (θ θ1 : Nat → Nat),
    run f θ gs = .ok θ1 → run f θ (gs ++ gs') = run f θ1 gs'
  | [],gs',θ,θ1,h => by
    simp only [run,Except.ok.injEq] at h
    subst h
    rfl
  | g :: gs,gs',θ,θ1,h => by
    simp only [List.cons_append,run] at h ⊢
    split at h
    · cases h
    · exact runAppend f gs gs' _ θ1 h

/-- Every compiled circuit runs: its output node holds the scalar value at
the positive inputs read from the even names, and even names as well as
names below the start node are untouched. -/
theorem circuitRun (f : Nat → Nat) (K : Nat) (hf : SelectedWithThreshold f K) {ι : Type} (index : ι → Nat) :
    ∀ (s : Scalar ι) (k : Nat) (θ : Nat → Nat),
      ∃ θ' : Nat → Nat, run f θ (circuitOf index s k).1 = .ok θ' ∧
        θ' (circuitOf index s k).2.1 = scalarValueWith f (fun x => θ (inputName (index x)) + 1) s ∧
        ∀ m, (m % 2 = 0 ∨ m < nodeName k) → θ' m = θ m
  | .one,k,θ => by
    refine ⟨Function.update θ (nodeName k) 1,?_,?_,?_⟩
    · exact singleRun f θ _ 1 (readAffine f θ _ _ 1 (by simp [NaturalAffineGateGraph.signedValue]))
    · show Function.update θ (nodeName k) 1 (nodeName k) = 1
      rw [Function.update_self]
    · intro m hm
      rw [Function.update_of_ne (by unfold nodeName at *; omega)]
  | .var x,k,θ => by
    refine ⟨Function.update θ (nodeName k) (θ (inputName (index x)) + 1),?_,?_,?_⟩
    · exact singleRun f θ _ _ (readAffine f θ _ _ _ (by simp [NaturalAffineGateGraph.signedValue]; omega))
    · show Function.update θ (nodeName k) (θ (inputName (index x)) + 1) (nodeName k) =
        θ (inputName (index x)) + 1
      rw [Function.update_self]
    · intro m hm
      rw [Function.update_of_ne (by unfold nodeName at *; omega)]
  | .add a b,k,θ => by
    obtain ⟨θa,ra,va,ea⟩ := circuitRun f K hf index a k θ
    obtain ⟨θb,rb,vb,eb⟩ := circuitRun f K hf index b (circuitOf index a k).2.2 θa
    have FA := circuitFacts index a k
    have FB := circuitFacts index b (circuitOf index a k).2.2
    have same : (fun x => θa (inputName (index x)) + 1) = (fun x => θ (inputName (index x)) + 1) := by
      funext x
      rw [ea _ (Or.inl (by unfold inputName; omega))]
    rw [same] at vb
    rw [circuitOf_add]
    generalize circuitOf index a k = A at *
    generalize circuitOf index b A.2.2 = B at *
    dsimp only
    obtain ⟨ka,oa,sa,_⟩ := FA
    obtain ⟨kb,ob,sb,_⟩ := FB
    have oaLt := (sa _ oa).2.2
    have keepA : θb A.2.1 = θa A.2.1 := eb _ (Or.inr oaLt)
    refine ⟨Function.update θb (nodeName B.2.2)
      (scalarValueWith f (fun x => θ (inputName (index x)) + 1) a +
        scalarValueWith f (fun x => θ (inputName (index x)) + 1) b),?_,?_,?_⟩
    · have r12 : run f θ (A.1 ++ B.1) = .ok θb := by
        rw [runAppend f A.1 B.1 θ θa ra]
        exact rb
      rw [runAppend f (A.1 ++ B.1) _ θ θb r12]
      refine singleRun f θb _ _ (readAffine f θb _ _ _ ?_)
      simp [NaturalAffineGateGraph.signedValue,keepA,va,vb]
    · show Function.update θb (nodeName B.2.2) _ (nodeName B.2.2) = _
      rw [Function.update_self]
      rfl
    · intro m hm
      rw [Function.update_of_ne (by unfold nodeName at *; omega)]
      rw [eb _ (by unfold nodeName at *; omega),ea _ hm]
  | .shift c a,k,θ => by
    obtain ⟨θa,ra,va,ea⟩ := circuitRun f K hf index a k θ
    have FA := circuitFacts index a k
    rw [circuitOf_shift]
    generalize circuitOf index a k = A at *
    dsimp only
    obtain ⟨ka,oa,sa,_⟩ := FA
    refine ⟨Function.update θa (nodeName A.2.2)
      (ParametricActualCollapse.collapseWith f
        (fixedHead c + (scalarValueWith f (fun x => θ (inputName (index x)) + 1) a : Ordinal))),?_,?_,?_⟩
    · rw [runAppend f A.1 _ θ θa ra]
      refine singleRun f θa _ _ ?_
      rw [readCollapse f K hf (scalarHeadNote c) A.2.1 (nodeName A.2.2) θa,va,headRepr]
    · show Function.update θa (nodeName A.2.2) _ (nodeName A.2.2) = _
      rw [Function.update_self]
      rfl
    · intro m hm
      rw [Function.update_of_ne (by unfold nodeName at *; omega),ea _ hm]

instance counterDecidable (tag x y : Nat) : Decidable (Counter tag x y) :=
  if h0 : tag = 0 then decidable_of_iff (y < x) (by simp [Counter,h0])
  else if h1 : tag = 1 then decidable_of_iff (y ≤ x) (by simp [Counter,h1])
  else decidable_of_iff (x ≠ y) (by simp [Counter,h0,h1])

theorem counterAnswer (tag a b : Nat) (θ : Nat → Nat) :
    OriginalMixedTerminalTest.rowAnswer θ (counterFormula tag a b) = true ↔ Counter tag (θ a) (θ b) := by
  unfold counterFormula Counter
  split_ifs <;>
    simp [OriginalMixedTerminalTest.rowAnswer,strictRow,weakRow,NormalForm.rowValue,
      NormalForm.Summand.term,Term.value] <;> omega

/-- The whole block runs from every base valuation, with both output nodes
holding the scalar values at the positive inputs `base (2 i) + 1`. -/
theorem blockRun (f : Nat → Nat) (K : Nat) (hf : SelectedWithThreshold f K) {ι : Type} (index : ι → Nat)
    (tag : Nat) (A B : Scalar ι) (base : Nat → Nat) :
    observe f base (block index tag A B).gates (.rows (block index tag A B).matrix) =
      .ok (decide (Counter tag (scalarValueWith f (fun x => base (inputName (index x)) + 1) A)
        (scalarValueWith f (fun x => base (inputName (index x)) + 1) B))) := by
  obtain ⟨θa,ra,va,ea⟩ := circuitRun f K hf index A 0 base
  obtain ⟨θb,rb,vb,eb⟩ := circuitRun f K hf index B (circuitOf index A 0).2.2 θa
  have FA := circuitFacts index A 0
  have same : (fun x => θa (inputName (index x)) + 1) = (fun x => base (inputName (index x)) + 1) := by
    funext x
    rw [ea _ (Or.inl (by unfold inputName; omega))]
  rw [same] at vb
  have keepA : θb (circuitOf index A 0).2.1 = θa (circuitOf index A 0).2.1 :=
    eb _ (Or.inr (FA.2.2.1 _ FA.2.1).2.2)
  have r : run f base (block index tag A B).gates = .ok θb := by
    show run f base ((circuitOf index A 0).1 ++ (circuitOf index B (circuitOf index A 0).2.2).1) = _
    rw [runAppend f _ _ base θa ra]
    exact rb
  unfold observe
  rw [r]
  show Except.ok (OriginalMixedTerminalTest.rowAnswer θb
    (counterFormula tag (circuitOf index A 0).2.1 (circuitOf index B (circuitOf index A 0).2.2).2.1)) = _
  congr 1
  have key := counterAnswer tag (circuitOf index A 0).2.1 (circuitOf index B (circuitOf index A 0).2.2).2.1 θb
  rw [keepA,va,vb] at key
  exact Bool.eq_iff_iff.mpr (key.trans decide_eq_true_iff.symm)

theorem blockCorrect : BlockCorrect := by
  intro f K hf ι index tag A B
  constructor
  · rintro ⟨base,hb⟩
    rw [blockRun f K hf index tag A B base] at hb
    have hc := of_decide_eq_true (Except.ok.inj hb)
    exact ⟨fun n => base (inputName n) + 1,fun n => Nat.succ_pos _,hc⟩
  · rintro ⟨ν,hpos,hc⟩
    refine ⟨fun m => ν (m / 2) - 1,?_⟩
    rw [blockRun f K hf index tag A B]
    have ev : (fun x => (fun m => ν (m / 2) - 1) (inputName (index x)) + 1) = (fun x => ν (index x)) := by
      funext x
      show ν (2 * index x / 2) - 1 + 1 = ν (index x)
      rw [Nat.mul_div_cancel_left _ (by decide)]
      have := hpos (index x)
      omega
    rw [ev]
    exact congrArg Except.ok (decide_eq_true hc)

theorem fullGroundScalarCircuit : FullGroundScalarCircuit := ⟨blockShape,blockCorrect⟩

#print axioms blockCorrect
#print axioms fullGroundScalarCircuit

end LogicLineages.PermittedControl.GroundScalarCircuit
