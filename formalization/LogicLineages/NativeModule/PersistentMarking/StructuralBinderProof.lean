module

public import LogicLineages.NativeModule.PersistentMarking.StructuralSubstitutionProof
public import LogicLineages.NativeModule.PersistentMarking.ClosingProof
public import LogicLineages.NativeModule.PersistentMarking.ClosingOpeningProof
public import LogicLineages.NativeModule.PersistentMarking.RefinementMarkProof

@[expose] public section

namespace LogicLineages.PersistentMarking.StructuralBinderProof
open Spine NameBridge StructuralContext

theorem openingMapOrdinary (S : Signature) (name : Name) (y : Nat) :
    StructuralStabilityTargets.OrdinaryMap S (openingMap name y) := by
  intro σ x
  by_cases he : (σ,x) = name <;> simp only [openingMap,he,if_true,if_false] <;>
    exact ⟨⟨.free,True.intro⟩,True.intro⟩

theorem binderPaper (S : Signature) (name : Name) (q : Expr) (τ : Ty) (h : PaperTerm S q τ) :
    PaperTerm S (.lam name.1 (close name q)) (.arrow name.1 τ) :=
  ⟨.lam (ClosingProof.closeTyped name q τ h.1),ClosingProof.closeValidity S name q h.2⟩

theorem weak (S : Signature) (name : Name) (s t : Expr) (τ : Ty)
    (hs : PaperTerm S s τ) (ht : PaperTerm S t τ) (ho : Ordinary t) (hw : Weak S s t) :
    Weak S (.lam name.1 (close name s)) (.lam name.1 (close name t)) := by
  obtain ⟨y,hfs,hft⟩ := OpeningFoundationProof.freshOpeningExists name.1 (close name s) (close name t)
  apply Weak.abs (binderPaper S name s τ hs) (binderPaper S name t τ ht) hfs hft
  rw [ClosingOpeningProof.closeOpen name y s τ hs.1,ClosingOpeningProof.closeOpen name y t τ ht.1]
  exact StructuralSubstitutionProof.weakMarked S s t (openingMap name y) ho (openingMapOrdinary S name y) hw

theorem strict (S : Signature) (name : Name) (s t : Expr) (τ : Ty)
    (hs : PaperTerm S s τ) (ht : PaperTerm S t τ) (ho : Ordinary t) (hw : Strict S s t) :
    Strict S (.lam name.1 (close name s)) (.lam name.1 (close name t)) := by
  cases hw with
  | @intro s σ t marked hq hp hm hweak =>
    have hmarked := RefinementMarkProof.markPaper S s τ marked hs hm
    have hc := SpineMarkingProof.covariance (closingMap name) 0 s marked hm
    apply Strict.intro (binderPaper S name s τ hs) (binderPaper S name t τ ht)
      (show mark (.lam name.1 (close name s)) = some (.lam name.1 (close name marked)) from by
        simp only [mark,close,hc,Option.map_some])
    exact weak S name marked t τ hmarked ht ho hweak
end LogicLineages.PersistentMarking.StructuralBinderProof
