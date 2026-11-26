import LogicLineages.PersistentMarking.UnaryBinderProof
namespace LogicLineages.PersistentMarking.UnarySelectionProof
open Spine UnaryTransportSupport UnaryTransportResults UnaryPermutationSupport

theorem arrowInput {υ τ : Ty} {a : Expr} (h : CallTyped EmptyContext υ (.cons a .nil) τ) :
    ∃ σ, υ = .arrow σ τ ∧ Typed EmptyContext a σ := by
  cases h with
  | cons ha hr => cases hr; exact ⟨_,rfl,ha⟩

theorem atValid {S : Signature} {qs : Args} {i : Nat} {q : Expr} (h : At qs i q) (hv : ValidArgs S qs) : Valid S q := by
  induction h with
  | here => exact hv.1
  | there _ ih => exact ih hv.2

theorem selectCase (S : Signature) (f : Head) (υ : Ty) (base extras : Args) (t q r : Expr)
    (domains : List Ty) (args : Args)
    (hp : PaperTerm S (.marked f υ base extras) υ) (ht : PaperTerm S t υ)
    (ha : At base i q ∨ At extras i q) (hq : Typed EmptyContext q (ArrowPrefix domains υ))
    (htuple : PrefixTuple f base extras domains args) (hcall : apply q args = some r)
    (hc : ExtendedWeakTree S r t) (ih : Unary S r t) : Unary S (.marked f υ base extras) t := by
  intro a b τ result hab hqa hsb hright
  obtain ⟨σ,hυ,hat⟩ := arrowInput hqa
  subst υ
  have htType := SpineShiftProof.annotationExact _ _ _ ht.1
  have hsb' : CallTyped EmptyContext (.arrow σ τ) (.cons b .nil) τ := htType ▸ hsb
  have hbt := (UnaryBinderProof.arrowArgument hsb').1
  have hargFacts : PaperTerm S a a.type ∧ PaperTerm S b b.type ∧ a.type = b.type := by
    obtain ⟨h⟩ := hab
    exact ExtendedEndpointProof.weakFacts h
  have hap : PaperTerm S a σ := ⟨hat,hargFacts.1.2⟩
  let es := extras.append (.cons a .nil)
  let Q := Expr.marked f σ base es
  have hpnew : PaperTerm S (.marked f τ base es) τ := newOwner S f (.arrow σ τ) τ σ base extras a hp hap
  have hQ : PaperTerm S Q σ := AuxiliaryReflexivityProof.retypePaper S f τ σ base es hpnew
  have hQb : ExtendedWeak S Q b := by
    have hh := newExtra hpnew hab
    have hbType := SpineShiftProof.annotationExact _ _ _ hbt
    simpa only [Q,hbType] using hh
  have hrType : r.type = .arrow σ τ := (ExtendedEndpointProof.weakFacts hc).2.2.trans htType
  have hQr : CallTyped EmptyContext r.type (.cons Q .nil) τ := by
    rw [hrType]
    exact .cons hQ.1 .nil
  obtain ⟨out,hout,hE⟩ := ih Q b τ result hQb hQr hsb hright
  have hqvalid : Valid S q := ha.elim (fun h => atValid h hp.2.2.1) (fun h => atValid h hp.2.2.2)
  have hfirst : PrefixTuple f base es domains args := tupleExtend htuple (.cons a .nil)
  have hsecond : PrefixTuple f base es [σ] (.cons Q .nil) := ConservativeOwnerSupport.wholeTuple f base es [σ]
  have hescape := PrefixEscapeProof.prefixEscape S f τ base es domains [σ] τ q args (.cons Q .nil) r out hpnew ⟨hq,hqvalid⟩ hfirst hsecond hcall hout
  have htarget : PaperTerm S result τ := by
    have htresult := SpineCallTypingProof.callPreserves EmptyContext t (.arrow σ τ) (.cons b .nil) τ result ht.1 hsb' hright
    obtain ⟨h⟩ := hE
    exact ⟨htresult,(ExtendedEndpointProof.weakFacts h).2.1.2⟩
  refine ⟨.marked f τ base es,markedCall hqa,?_⟩
  rcases hescape with hfull | href
  · have hq' : Typed EmptyContext q (ArrowPrefix (domains ++ [σ]) τ) := by
      simpa only [arrowAppend,ArrowPrefix] using hq
    have hat' : At base i q ∨ At es i q := ha.elim Or.inl (fun h => Or.inr (RefinementAppendProof.atLeft (.cons a .nil) h))
    obtain ⟨hcont⟩ := hE
    exact ⟨.pselect hpnew htarget hat' hq' (tupleAppend hfirst hsecond) hfull hcont⟩
  · exact SharpAdmissibleProof.weak S _ _ _ href hE
end LogicLineages.PersistentMarking.UnarySelectionProof
