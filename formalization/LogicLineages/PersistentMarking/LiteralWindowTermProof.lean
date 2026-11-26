import LogicLineages.PersistentMarking.LiteralWindowSupportProof
import LogicLineages.PersistentMarking.NumberedWindowSourceGuardChecks
import LogicLineages.PersistentMarking.DecisionSourceOwnerProof
import LogicLineages.PersistentMarking.DecisionSourceCallProof

namespace LogicLineages.PersistentMarking.LiteralWindowTermProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionSourceUniverse
open TypeSupport (subtypes)
open LiteralWindowSupportProof NumberedWindowSourceGuardTargets

theorem opened {S : Signature} {K : List Ty} {σ τ : Ty} {body : Expr}
    (h : PaperTerm S (.lam σ body) (.arrow σ τ)) (hW : TermIn K (.lam σ body)) (x : Nat) :
    TermIn K (openBody σ x body) := by
  have hBody : Spine.Typed (EmptyContext.push σ) body τ := by
    cases h.1 with
    | lam ht => exact ht
  have hv : SourceValues S K EmptyContext [σ] (.cons (.free σ x) .nil) :=
    ⟨.cons .free .nil,⟨True.intro,True.intro⟩,join (lamDomain hW) empty⟩
  exact (NumberedWindowSourceGuardChecks.exact_ActualBlockGuard
    S K EmptyContext [σ] (.cons (.free σ x) .nil) body τ ⟨hBody,h.2,lamBody hW⟩ hv).2.2

theorem markIn {K : List Ty} {q r : Expr} (hW : TermIn K q) (h : mark q = some r) : TermIn K r :=
  fun ρ hr => hW ρ ((DecisionSourceMarkProof.markFacts q r h).1 ρ hr)

theorem fabsSource {K : List Ty} {f : Head} {σ τ : Ty} {bs es : Spine.Args} (x : Nat)
    (h : TermIn K (.marked f (.arrow σ τ) bs es)) :
    TermIn K (.marked f τ bs (es.append (.cons (.free σ x) .nil))) := by
  obtain ⟨hd,ht,hb,he⟩ := markedParts h
  exact markedBuild hd (arrowResult ht) hb
    (argsJoin es (.cons (.free σ x) .nil) he (join (arrowDomain ht) empty))

theorem universeArgsIn {K : List Ty} {V : List Name} {H : List Head} {Γ : Context}
    (xs : Spine.Args) (h : ArgsUniverse K V H Γ xs) : ArgsIn K xs := by
  cases xs with
  | nil => exact empty
  | cons b rest => exact join h.1.1 (universeArgsIn rest h.2)
termination_by sizeOf xs

private theorem callOwner (f : Head) (τ : Ty) (bs es : Spine.Args) (ds : List Ty)
    (ht : Spine.Typed EmptyContext (.marked f τ bs es) τ) :
    CallTyped EmptyContext (ArrowPrefix ds τ) (Spine.ownerCopies f bs es ds) τ := by
  cases ht with
  | marked hb he =>
    induction ds with
    | nil => exact .nil
    | cons σ rest ih => exact .cons (.marked hb he) ih

theorem selectFacts {K : List Ty} {f : Head} {τ : Ty} {bs es : Spine.Args}
    {i : Nat} {q r : Expr} {ds : List Ty}
    (hk : DecisionSourceUniverse.Closed K)
    (hOwn : TermIn K (.marked f τ bs es))
    (hTyped : Spine.Typed EmptyContext (.marked f τ bs es) τ)
    (hAt : At bs i q ∨ At es i q) (hQ : Spine.Typed EmptyContext q (ArrowPrefix ds τ))
    (hCall : apply q (Spine.ownerCopies f bs es ds) = some r) :
    TermIn K q ∧ Covers K (subtypes (ArrowPrefix ds τ)) ∧
      ArgsIn K (Spine.ownerCopies f bs es ds) ∧ TermIn K r := by
  let owner := Expr.marked f τ bs es
  let V := freeInventory owner
  let H := heads owner
  have ho : Universe K V H [] owner :=
    ⟨hOwn,fun _ h => h,fun n h => Or.inl ((DecisionInventoryProof.freeExact owner n).mpr h)⟩
  have hSelected : Universe K V H [] q := hAt.elim
    (fun h => DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _
      (DecisionSourceBasicProof.markedBase _ _ _ _ _ _ _ _ ho) h)
    (fun h => DecisionSourceBasicProof.sourceAt _ _ _ _ _ _ _
      (DecisionSourceBasicProof.markedExtras _ _ _ _ _ _ _ _ ho) h)
  have hCopies := DecisionSourceOwnerProof.ownerTuple K V H [] f τ bs es ds q i hk ho hAt hQ
  have hArgs := callOwner f τ bs es ds hTyped
  have hResult := DecisionSourceCallProof.fullCall K V H [] q (ArrowPrefix ds τ)
    (Spine.ownerCopies f bs es ds) τ r hk hQ hArgs hSelected hCopies hCall
  have hType := SpineShiftProof.annotationExact _ _ _ hQ
  have hRoot : ArrowPrefix ds τ ∈ K := hType ▸ rootIn hSelected.1
  exact ⟨hSelected.1,hk _ hRoot,universeArgsIn _ hCopies,hResult.1⟩

end LogicLineages.PersistentMarking.LiteralWindowTermProof
