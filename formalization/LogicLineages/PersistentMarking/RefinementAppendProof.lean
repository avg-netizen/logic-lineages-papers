import LogicLineages.PersistentMarking.RefinementAppendTargets
import LogicLineages.PersistentMarking.RefinementSubstitutionProof
namespace LogicLineages.PersistentMarking.RefinementAppendProof
open Spine AuxiliaryReflexivityProof

theorem atLeft {xs i q} (ys : Args) (h : At xs i q) : At (xs.append ys) i q := by
  induction h with
  | here => exact .here
  | there _ ih => exact .there ih

theorem atRight (xs : Args) {ys i q} (h : At ys i q) : ∃ j, At (xs.append ys) j q := by
  cases xs with
  | nil => exact ⟨i,h⟩
  | cons x xs =>
    obtain ⟨j,hj⟩ := atRight xs h
    exact ⟨j+1,.there hj⟩
termination_by sizeOf xs

theorem argsFacts {S : Signature} {qs ss : Args} (h : RefinementBasesTree S qs ss) :
    ExtrasTyped EmptyContext qs ∧ ValidArgs S qs ∧ ExtrasTyped EmptyContext ss ∧ ValidArgs S ss := by
  cases h with
  | nil => exact ⟨.nil,True.intro,.nil,True.intro⟩
  | cons h hs =>
    have hp := RefinementSubstitutionSupport.endpoints h
    have ht := argsFacts hs
    exact ⟨.cons hp.1.1 ht.1,⟨hp.1.2,ht.2.1⟩,.cons hp.2.1 ht.2.2.1,⟨hp.2.2,ht.2.2.2⟩⟩
termination_by sizeOf ss

theorem typedAppend {Γ : BoundContext} {xs ys : Args} (hx : ExtrasTyped Γ xs) (hy : ExtrasTyped Γ ys) : ExtrasTyped Γ (xs.append ys) := by
  cases xs with
  | nil => exact hy
  | cons x xs =>
    cases hx with
    | cons h hs => exact .cons h (typedAppend hs hy)
termination_by sizeOf xs

theorem validAppend (S : Signature) (xs ys : Args) (hx : ValidArgs S xs) (hy : ValidArgs S ys) : ValidArgs S (xs.append ys) := by
  cases xs with
  | nil => exact hy
  | cons x xs => exact ⟨hx.1,validAppend S xs ys hx.2 hy⟩
termination_by sizeOf xs

theorem appendPaper (S : Signature) (f : Head) (σ τ : Ty) (base extras tail : Args)
    (hp : PaperTerm S (.marked f σ base extras) σ) (ht : ExtrasTyped EmptyContext tail) (hv : ValidArgs S tail) :
    PaperTerm S (.marked f τ base (extras.append tail)) τ := by
  cases hp.1 with
  | marked hb he => exact ⟨.marked hb (typedAppend he ht),hp.2.1,hp.2.2.1,validAppend S extras tail hp.2.2.2 hv⟩

theorem omitSuffix : RefinementAppendTargets.OmitSuffix := by
  intro S f τ base extras tail hnew hold
  cases hold.1 with
  | marked hb he =>
    obtain ⟨hbase⟩ := refinementBasesRefl S base _ hb hold.2.2.1
    obtain ⟨hextras⟩ := refinementExtrasRefl S f base (extras.append tail) extras he hold.2.2.2 (fun i q h => ⟨i,atLeft tail h⟩)
    exact ⟨.marked hnew hold hbase hextras⟩

theorem extendExtra (S : Signature) (f : Head) (σ : Ty) (base extras tail : Args) (q : Expr)
    (hold : PaperTerm S (.marked f σ base extras) σ) (hnew : PaperTerm S (.marked f σ base (extras.append tail)) σ)
    (h : RefinementExtraTree S f base extras q) :
    _root_.Nonempty (RefinementExtraTree S f base (extras.append tail) q) := by
  cases h with
  | existing ha hc => exact ⟨.existing (atLeft tail ha) hc⟩
  | owner hc =>
    have homit := omitSuffix S f q.type base extras tail
      (retypePaper S f σ q.type base (extras.append tail) hnew) (retypePaper S f σ q.type base extras hold)
    obtain ⟨hcomp⟩ := RefinementTransitivityProof.transitive S _ _ _ homit ⟨hc⟩
    exact ⟨.owner hcomp⟩

theorem extendExtras (S : Signature) (f : Head) (σ : Ty) (base extras tail qs : Args)
    (hold : PaperTerm S (.marked f σ base extras) σ) (hnew : PaperTerm S (.marked f σ base (extras.append tail)) σ)
    (h : RefinementExtrasTree S f base extras qs) :
    _root_.Nonempty (RefinementExtrasTree S f base (extras.append tail) qs) := by
  cases qs with
  | nil => exact ⟨.nil⟩
  | cons q qs =>
    cases h with
    | cons h hs =>
      obtain ⟨h'⟩ := extendExtra S f σ base extras tail _ hold hnew h
      obtain ⟨hs'⟩ := extendExtras S f σ base extras tail _ hold hnew hs
      exact ⟨.cons h' hs'⟩
termination_by sizeOf qs

theorem newExtras (S : Signature) (f : Head) (base full qs ss : Args)
    (h : RefinementBasesTree S qs ss) (occ : ∀ i q, At qs i q → ∃ j, At full j q) :
    _root_.Nonempty (RefinementExtrasTree S f base full ss) := by
  cases h with
  | nil => exact ⟨.nil⟩
  | cons h hs =>
    obtain ⟨j,hj⟩ := occ 0 _ .here
    obtain ⟨tail⟩ := newExtras S f base full _ _ hs (fun i q ha => occ (i+1) q (.there ha))
    exact ⟨.cons (.existing hj h) tail⟩
termination_by sizeOf ss

theorem appendWitness {S : Signature} {f : Head} {base full xs ys : Args}
    (hx : RefinementExtrasTree S f base full xs) (hy : RefinementExtrasTree S f base full ys) :
    _root_.Nonempty (RefinementExtrasTree S f base full (xs.append ys)) := by
  cases xs with
  | nil => exact ⟨hy⟩
  | cons x xs =>
    cases hx with
    | cons h hs =>
      obtain ⟨tail⟩ := appendWitness hs hy
      exact ⟨.cons h tail⟩
termination_by sizeOf xs

theorem markedAppend : RefinementAppendTargets.MarkedAppend := by
  intro S f σ τ qb qe sb se as bs h hab
  obtain ⟨h⟩ := h
  obtain ⟨hab⟩ := hab
  have hf := argsFacts hab
  cases h with
  | marked hp hs hb he =>
    have hpn := appendPaper S f σ σ qb qe as hp hf.1 hf.2.1
    have hsn := appendPaper S f σ σ sb se bs hs hf.2.2.1 hf.2.2.2
    obtain ⟨hold⟩ := extendExtras S f σ qb qe as se hp hpn he
    obtain ⟨hnew⟩ := newExtras S f qb (qe.append as) as bs hab (fun _ _ h => atRight qe h)
    obtain ⟨hall⟩ := appendWitness hold hnew
    exact ⟨.marked (retypePaper S f σ τ qb (qe.append as) hpn) (retypePaper S f σ τ sb (se.append bs) hsn) hb hall⟩

theorem headAppend : RefinementAppendTargets.HeadAppend := by
  intro S f τ qb sb as bs h hab
  obtain ⟨h⟩ := h
  cases h with
  | head hp hs hb =>
    have hpm : PaperTerm S (.marked f f.result qb .nil) f.result := by
      cases hp.1 with
      | head ht => exact ⟨.marked ht .nil,hp.2.1,hp.2.2,True.intro⟩
    have hsm : PaperTerm S (.marked f f.result sb .nil) f.result := by
      cases hs.1 with
      | head ht => exact ⟨.marked ht .nil,hs.2.1,hs.2.2,True.intro⟩
    exact markedAppend S f f.result τ qb .nil sb .nil as bs ⟨.marked hpm hsm hb .nil⟩ hab
end LogicLineages.PersistentMarking.RefinementAppendProof
