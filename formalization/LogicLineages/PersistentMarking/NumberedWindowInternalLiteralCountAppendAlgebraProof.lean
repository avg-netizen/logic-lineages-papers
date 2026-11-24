module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendCoreProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAllQueriesTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountConverseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountTupleProof
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsBindingProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionCancellationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAlgebraProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppend (append)
open ID1Completion.InternalClosedProgramsBindingProof (actualFiniteUniversalIntroduction)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn eqnRelabel varBind liftBind)
open ID1Completion.InternalTagArithmeticSupportProof (symm trans congTerm)
open ID1Completion.InternalAdditionLawsProof (add addSubst congAddLeft associativity)
open ID1Completion.InternalAdditionCancellationProof (commutativity)
open NumberedWindowInternalLiteralCountAppendCoreProof (appended)
open NumberedWindowInternalLiteralCountAppendProof (exact_LiteralOpenCountAppend)
open NumberedWindowInternalLiteralCountAllQueriesTargets (agreement agreementBody)
open NumberedWindowInternalLiteralCountConverseProof (exact_LiteralAgreementAccept)
open NumberedWindowInternalLiteralCountTupleProof (openCountTuple)
open NumberedWindowInternalLiteralCount (entryCount permutation)
open NumberedWindowInternalLiteralCountSupportedTargets (counted)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def congFirst (r : OTerm α) {s t : OTerm α}
    (h : Derivation B Γ (eqn s t)) : Derivation B Γ (eqn (add s r) (add t r)) := by
  have e := congTerm (add (.var (.inr (0 : Fin 1))) (r.relabel Sum.inl)) h
  simpa only [addSubst,varBind,liftBind] using e

private def middleSwapSum (a b c d : OTerm α) :
    Derivation B Γ (eqn (add (add a b) (add c d)) (add (add a c) (add b d))) := by
  have inA : Derivation B Γ (eqn (add b (add c d)) (add c (add b d))) :=
    trans (symm (associativity b c d))
      (trans (congFirst d (commutativity b c)) (associativity c b d))
  exact trans (associativity a b (add c d))
    (trans (congAddLeft a inA) (symm (associativity a c (add b d))))

private theorem introAgreement (left right : OTerm α)
    (each : ∀ (β : Type) (j : α → β) (Δ : List (Formula β)) (key lc rc : OTerm β),
      (∀ f ∈ Γ, f.relabel j ∈ Δ) →
      Nonempty (Derivation B Δ (counted (left.relabel j) key lc)) →
      Nonempty (Derivation B Δ (counted (right.relabel j) key rc)) →
      Nonempty (Derivation B Δ (eqn lc rc))) : Nonempty (Derivation B Γ (agreement left right)) := by
  unfold agreement
  apply actualFiniteUniversalIntroduction B α 3 Γ (agreementBody left right)
  let j : α → α ⊕ Fin 3 := Sum.inl
  let key : OTerm (α ⊕ Fin 3) := .var (.inr 0)
  let lc : OTerm (α ⊕ Fin 3) := .var (.inr 1)
  let rc : OTerm (α ⊕ Fin 3) := .var (.inr 2)
  let H := counted (left.relabel j) key lc ⊓ counted (right.relabel j) key rc
  let Δ := H :: Γ.map (fun q => q.relabel j)
  have keep : ∀ f ∈ Γ, f.relabel j ∈ Δ := by
    intro f hf
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
  have own : Derivation B Δ H := Derivation.hypothesis List.mem_cons_self
  obtain ⟨e⟩ := each (α ⊕ Fin 3) j Δ key lc rc keep
    ⟨Derivation.conjunctionLeft own⟩ ⟨Derivation.conjunctionRight own⟩
  exact ⟨Derivation.implicationIntroduction e⟩

/-- Compare two held ordered append recipes by internal multiplicity. -/
theorem exact_LiteralAppendAssociativity (a b c ab bc left right : OTerm α)
    (hab : Nonempty (Derivation B Γ (appended a b ab)))
    (hbc : Nonempty (Derivation B Γ (appended b c bc)))
    (hleft : Nonempty (Derivation B Γ (appended ab c left)))
    (hright : Nonempty (Derivation B Γ (appended a bc right)))
    : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])) := by
  apply exact_LiteralAgreementAccept B α Γ left right
  apply introAgreement left right
  intro β j Δ key lc rc keep l r
  let A := a.relabel j
  let Bterm := b.relabel j
  let C := c.relabel j
  let AB := ab.relabel j
  let BC := bc.relabel j
  let LEFT := left.relabel j
  let RIGHT := right.relabel j
  have pab := renamePair append ab a b hab j keep
  have pbc := renamePair append bc b c hbc j keep
  have pleft := renamePair append left ab c hleft j keep
  have pright := renamePair append right a bc hright j keep
  let codes : Fin 5 → OTerm β := ![A,Bterm,C,AB,BC]
  apply openCountTuple codes key (eqn lc rc)
  intro γ k Ω vals retain pay
  let va := vals 0
  have ca : Nonempty (Derivation B Ω (counted (A.relabel k) (key.relabel k) va)) :=
    pay (0 : Fin 5)
  let vb := vals 1
  have cb : Nonempty (Derivation B Ω (counted (Bterm.relabel k) (key.relabel k) vb)) :=
    pay (1 : Fin 5)
  let vc := vals 2
  have cc : Nonempty (Derivation B Ω (counted (C.relabel k) (key.relabel k) vc)) :=
    pay (2 : Fin 5)
  let vab := vals 3
  have cab : Nonempty (Derivation B Ω (counted (AB.relabel k) (key.relabel k) vab)) :=
    pay (3 : Fin 5)
  let vbc := vals 4
  have cbc : Nonempty (Derivation B Ω (counted (BC.relabel k) (key.relabel k) vbc)) :=
    pay (4 : Fin 5)
  let vleft := lc.relabel k
  let vright := rc.relabel k
  have cleft := renamePair entryCount lc LEFT key l k retain
  have cright := renamePair entryCount rc RIGHT key r k retain
  obtain ⟨eab⟩ := exact_LiteralOpenCountAppend (A.relabel k) (Bterm.relabel k)
    (key.relabel k) (AB.relabel k) va vb vab
    (renamePair append AB A Bterm pab k retain) ca cb cab
  obtain ⟨ebc⟩ := exact_LiteralOpenCountAppend (Bterm.relabel k) (C.relabel k)
    (key.relabel k) (BC.relabel k) vb vc vbc
    (renamePair append BC Bterm C pbc k retain) cb cc cbc
  obtain ⟨eleft⟩ := exact_LiteralOpenCountAppend (AB.relabel k) (C.relabel k)
    (key.relabel k) (LEFT.relabel k) vab vc vleft
    (renamePair append LEFT AB C pleft k retain) cab cc cleft
  obtain ⟨eright⟩ := exact_LiteralOpenCountAppend (A.relabel k) (BC.relabel k)
    (key.relabel k) (RIGHT.relabel k) va vbc vright
    (renamePair append RIGHT A BC pright k retain) ca cbc cright
  rw [eqnRelabel]
  have eqL := trans eleft (congFirst vc eab)
  have eqR := trans eright (congAddLeft va ebc)
  exact ⟨trans eqL (trans (associativity va vb vc) (symm eqR))⟩


/-- Compare two held ordered append recipes by internal multiplicity. -/
theorem exact_LiteralAppendMiddleInterchange (a b c d ab cd ac bd left right : OTerm α)
    (hab : Nonempty (Derivation B Γ (appended a b ab)))
    (hcd : Nonempty (Derivation B Γ (appended c d cd)))
    (hac : Nonempty (Derivation B Γ (appended a c ac)))
    (hbd : Nonempty (Derivation B Γ (appended b d bd)))
    (hleft : Nonempty (Derivation B Γ (appended ab cd left)))
    (hright : Nonempty (Derivation B Γ (appended ac bd right)))
    : Nonempty (Derivation B Γ (programGraph permutation (suc z) ![left,right])) := by
  apply exact_LiteralAgreementAccept B α Γ left right
  apply introAgreement left right
  intro β j Δ key lc rc keep l r
  let A := a.relabel j
  let Bterm := b.relabel j
  let C := c.relabel j
  let D := d.relabel j
  let AB := ab.relabel j
  let CD := cd.relabel j
  let AC := ac.relabel j
  let BD := bd.relabel j
  let LEFT := left.relabel j
  let RIGHT := right.relabel j
  have pab := renamePair append ab a b hab j keep
  have pcd := renamePair append cd c d hcd j keep
  have pac := renamePair append ac a c hac j keep
  have pbd := renamePair append bd b d hbd j keep
  have pleft := renamePair append left ab cd hleft j keep
  have pright := renamePair append right ac bd hright j keep
  let codes : Fin 8 → OTerm β := ![A,Bterm,C,D,AB,CD,AC,BD]
  apply openCountTuple codes key (eqn lc rc)
  intro γ k Ω vals retain pay
  let va := vals 0
  have ca : Nonempty (Derivation B Ω (counted (A.relabel k) (key.relabel k) va)) :=
    pay (0 : Fin 8)
  let vb := vals 1
  have cb : Nonempty (Derivation B Ω (counted (Bterm.relabel k) (key.relabel k) vb)) :=
    pay (1 : Fin 8)
  let vc := vals 2
  have cc : Nonempty (Derivation B Ω (counted (C.relabel k) (key.relabel k) vc)) :=
    pay (2 : Fin 8)
  let vd := vals 3
  have cd : Nonempty (Derivation B Ω (counted (D.relabel k) (key.relabel k) vd)) :=
    pay (3 : Fin 8)
  let vab := vals 4
  have cab : Nonempty (Derivation B Ω (counted (AB.relabel k) (key.relabel k) vab)) :=
    pay (4 : Fin 8)
  let vcd := vals 5
  have ccd : Nonempty (Derivation B Ω (counted (CD.relabel k) (key.relabel k) vcd)) :=
    pay (5 : Fin 8)
  let vac := vals 6
  have cac : Nonempty (Derivation B Ω (counted (AC.relabel k) (key.relabel k) vac)) :=
    pay (6 : Fin 8)
  let vbd := vals 7
  have cbd : Nonempty (Derivation B Ω (counted (BD.relabel k) (key.relabel k) vbd)) :=
    pay (7 : Fin 8)
  let vleft := lc.relabel k
  let vright := rc.relabel k
  have cleft := renamePair entryCount lc LEFT key l k retain
  have cright := renamePair entryCount rc RIGHT key r k retain
  obtain ⟨eab⟩ := exact_LiteralOpenCountAppend (A.relabel k) (Bterm.relabel k)
    (key.relabel k) (AB.relabel k) va vb vab
    (renamePair append AB A Bterm pab k retain) ca cb cab
  obtain ⟨ecd⟩ := exact_LiteralOpenCountAppend (C.relabel k) (D.relabel k)
    (key.relabel k) (CD.relabel k) vc vd vcd
    (renamePair append CD C D pcd k retain) cc cd ccd
  obtain ⟨eac⟩ := exact_LiteralOpenCountAppend (A.relabel k) (C.relabel k)
    (key.relabel k) (AC.relabel k) va vc vac
    (renamePair append AC A C pac k retain) ca cc cac
  obtain ⟨ebd⟩ := exact_LiteralOpenCountAppend (Bterm.relabel k) (D.relabel k)
    (key.relabel k) (BD.relabel k) vb vd vbd
    (renamePair append BD Bterm D pbd k retain) cb cd cbd
  obtain ⟨eleft⟩ := exact_LiteralOpenCountAppend (AB.relabel k) (CD.relabel k)
    (key.relabel k) (LEFT.relabel k) vab vcd vleft
    (renamePair append LEFT AB CD pleft k retain) cab ccd cleft
  obtain ⟨eright⟩ := exact_LiteralOpenCountAppend (AC.relabel k) (BD.relabel k)
    (key.relabel k) (RIGHT.relabel k) vac vbd vright
    (renamePair append RIGHT AC BD pright k retain) cac cbd cright
  rw [eqnRelabel]
  have eqL := trans eleft (trans (congFirst vcd eab) (congAddLeft (add va vb) ecd))
  have eqR := trans eright (trans (congFirst vbd eac) (congAddLeft (add va vc) ebd))
  exact ⟨trans eqL (trans (middleSwapSum va vb vc vd) (symm eqR))⟩

#print axioms exact_LiteralAppendAssociativity
#print axioms exact_LiteralAppendMiddleInterchange
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCountAppendAlgebraProof
