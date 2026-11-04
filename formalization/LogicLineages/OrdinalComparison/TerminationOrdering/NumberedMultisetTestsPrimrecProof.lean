module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetTestsPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetPresentationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteMarkPrimrecProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeGuardsPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetTestsPrimrecProof
open Source NumberedRewriteReduction NumberedMarkCertificate NumberedMultisetCertificate

local instance {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} :
    DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq

private theorem optionAnyPrimitive {A B : Type} [Primcodable A] [Primcodable B]
    {f : A → Option B} {g : A → B → Bool} (hf : Primrec f) (hg : Primrec₂ g) :
    Primrec (fun a => (f a).any (g a)) :=
  (Primrec.option_casesOn hf (Primrec.const false) hg).of_eq (by
    intro a; cases f a <;> rfl)

def witnessTest {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (removed : List (Packed (Fin n) arity Gamma)) (q : Packed (Fin n) arity Gamma)
    (witness : MarkWitness) : Bool :=
  (removed[witness.1]?).any (fun s => decide (markTarget witness.2 s = some q))

theorem witnessTestPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
        Packed (Fin n) arity Gamma × MarkWitness => witnessTest p.1 p.2.1 p.2.2) := by
  apply optionAnyPrimitive
    (Primrec.list_getElem?.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
  exact ((Primrec.eq.comp
    ((NumberedFiniteMarkPrimrecProof.markTargetPrimitive n arity Gamma).comp
      ((Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))
    (Primrec.option_some.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)))).decide).to₂

def replacementStep {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (removed : List (Packed (Fin n) arity Gamma))
    (state : List (Packed (Fin n) arity Gamma) × Bool) (witness : MarkWitness) :
    List (Packed (Fin n) arity Gamma) × Bool :=
  (state.1.tail,state.2 && state.1.head?.any (fun q => witnessTest removed q witness))

def replacementFinish {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (state : List (Packed (Fin n) arity Gamma) × Bool) : Bool :=
  decide (state.1 = []) && state.2

theorem replacementFoldCalibration {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (removed inserted : List (Packed (Fin n) arity Gamma)) (witnesses : List MarkWitness)
    (valid : Bool) :
    replacementFinish (witnesses.foldl (replacementStep removed) (inserted,valid)) =
      (valid && replacementTest removed inserted witnesses) := by
  induction witnesses generalizing inserted valid with
  | nil => cases inserted <;> cases valid <;> rfl
  | cons witness witnesses ih =>
    rcases witness with ⟨index,label⟩
    cases inserted with
    | nil =>
      simpa [List.foldl_cons, replacementStep, replacementFinish, replacementTest] using
        (ih [] false)
    | cons q rest =>
      simp only [List.foldl_cons, replacementStep, List.tail_cons, List.head?_cons, Option.any_some]
      rw [ih]
      cases h : removed[index]? with
      | none => simp [witnessTest, h, replacementTest]
      | some s => simp [witnessTest, h, replacementTest, Bool.and_assoc]

theorem replacementStepPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
        (List (Packed (Fin n) arity Gamma) × Bool) × MarkWitness =>
      replacementStep p.1 p.2.1 p.2.2) := by
  have ht : Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
      (List (Packed (Fin n) arity Gamma) × Bool) × MarkWitness => p.2.1.1.tail) :=
    Primrec.list_tail.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
  have hh : Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
      (List (Packed (Fin n) arity Gamma) × Bool) × MarkWitness =>
      p.2.1.1.head?.any (fun q => witnessTest p.1 q p.2.2)) :=
    optionAnyPrimitive
      (Primrec.list_head?.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))
      ((witnessTestPrimitive n arity Gamma).comp
        ((Primrec.fst.comp Primrec.fst).pair
          (Primrec.snd.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))))).to₂
  exact ht.pair (Primrec.and.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)) hh)

theorem replacementTestPrimitive :
    NumberedMultisetTestsPrimrecTargets.ActualReplacementTestPrimitive := by
  intro n arity Gamma
  have hfold : Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
      List (Packed (Fin n) arity Gamma) × List MarkWitness =>
      p.2.2.foldl (replacementStep p.1) (p.2.1,true)) :=
    Primrec.list_foldl (Primrec.snd.comp Primrec.snd)
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.const true))
      ((replacementStepPrimitive n arity Gamma).comp
        ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have hfinish : Primrec (@replacementFinish n arity Gamma) :=
    Primrec.and.comp (Primrec.eq.comp Primrec.fst (Primrec.const [])).decide Primrec.snd
  exact (hfinish.comp hfold).of_eq (by
    intro p
    simpa using replacementFoldCalibration p.1 p.2.1 p.2.2 true)

theorem multisetTestPrimitive :
    NumberedMultisetTestsPrimrecTargets.ActualMultisetTestPrimitive := by
  intro n arity Gamma
  have hc : Primrec (fun p : List (Packed (Fin n) arity Gamma) ×
      List (Packed (Fin n) arity Gamma) × MultisetCertificate n arity Gamma =>
      NumberedMultisetPresentation.certificateEquiv n arity Gamma p.2.2) :=
    (NumberedMultisetPresentationProof.certificateFieldsPrimitive n arity Gamma).comp
      (Primrec.snd.comp Primrec.snd)
  have hk := Primrec.fst.comp hc
  have hr := Primrec.fst.comp (Primrec.snd.comp hc)
  have hi := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hw := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hc))
  have hp := NumberedExchangeGuardsPrimrecProof.permutationPrimitive (Packed (Fin n) arity Gamma)
  have hleft := hp.comp (Primrec.fst.pair (Primrec.list_append.comp hk hr))
  have hright := hp.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.list_append.comp hk hi))
  have hnonempty := (Primrec.eq.comp hr (Primrec.const [])).not.decide
  have hwitnesses := (replacementTestPrimitive n arity Gamma).comp (hr.pair (hi.pair hw))
  exact (Primrec.and.comp (Primrec.and.comp hleft (Primrec.and.comp hright hnonempty)) hwitnesses).of_eq
    (by
      intro p
      simp only [multisetTest, NumberedMultisetPresentation.certificateEquiv, Bool.decide_and]
      rfl)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetTestsPrimrecProof
