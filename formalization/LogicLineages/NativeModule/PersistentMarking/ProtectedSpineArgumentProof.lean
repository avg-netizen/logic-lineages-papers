module

public import LogicLineages.NativeModule.PersistentMarking.ProtectedSpineEncodingProof
public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTupleProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ProtectedSpineArgumentProof
open Spine DecisionPorts FiniteDomainSchema HereditaryDomainCode HereditaryDomainSemantics
open ProtectedSpineEnvironment ProtectedSpineInterpreterCore ProtectedSpineLaws

def consArguments (E : Environment) (σ : Ty) (ev : Evaluation) (tail : Arguments) : Arguments :=
  fun Γ free bound => (σ,codeAt E σ ev Γ ⟨free,bound⟩)::tail Γ free bound

theorem nil (E : Environment) : ArgumentLaws E (fun _ _ _ => []) [] := by
  refine ⟨fun _ _ => rfl, fun Γ _ _ => HereditaryTupleProof.tupleNil E Γ,fun _ _ _ _ _ _ => rfl,?_⟩
  intro Γ a b _ _ _ i σ x y hσ
  cases i <;> cases hσ

theorem cons (E : Environment) (σ : Ty) (ev : Evaluation) (types : List Ty) (tail : Arguments)
    (hl : EvaluationLaws E σ ev) (ht : ArgumentLaws E tail types) :
    ArgumentLaws E (consArguments E σ ev tail) (σ::types) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro Γ a
    change σ::(argumentValues tail Γ a).map Prod.fst = σ::types
    rw [ht.types_eq Γ a]
  · intro Γ a ha
    change TupleValues E Γ (σ::types) (codeAt E σ ev Γ a :: (argumentValues tail Γ a).map Prod.snd)
    exact (HereditaryTupleProof.tupleCons E Γ σ types _ _).mpr
      ⟨(ProtectedSpineEncodingProof.encodeAt E σ ev hl Γ a ha).1,ht.valid Γ a ha⟩
  · intro Γ Δ a ha hd he
    change (σ,(descriptor E σ).restrict Γ Δ (codeAt E σ ev Γ a)) ::
        weakenBound E Γ Δ (argumentValues tail Γ a) =
      (σ,codeAt E σ ev Δ (a.restrict E Γ Δ)) :: argumentValues tail Δ (a.restrict E Γ Δ)
    rw [ProtectedSpineEncodingProof.codeNatural E σ ev hl Γ Δ a ha hd he,ht.natural Γ Δ a ha hd he]
  · intro Γ a b ha hb hab
    change ValuesLE E Γ (σ::types) (codeAt E σ ev Γ a :: (argumentValues tail Γ a).map Prod.snd)
      (codeAt E σ ev Γ b :: (argumentValues tail Γ b).map Prod.snd)
    exact (MarkedBaseTupleFoundationProof.valuesCons E Γ σ types _ _ _ _).mpr
      ⟨ProtectedSpineEncodingProof.codeOrder E σ ev hl Γ a b ha hb hab,ht.monotone Γ a b ha hb hab⟩

theorem zipProjections (xs : BoundValues) : (xs.map Prod.fst).zip (xs.map Prod.snd) = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    rcases a with ⟨σ,c⟩
    simp only [List.map_cons,List.zip_cons_cons,ih]

theorem tags (E : Environment) (Γ : Context) (args : Arguments) (types : List Ty) (a : Assignments)
    (hl : ArgumentLaws E args types) (ha : InputValid E Γ a)
    (ht : ∀ σ, σ ∈ types → σ ∈ E.types) (p : MarkedExtras.Tagged) (hp : p ∈ argumentValues args Γ a) :
    p ∈ MarkedExtras.«universe» E Γ := by
  have hc : (argumentValues args Γ a).map Prod.fst = types := hl.types_eq Γ a
  have hz : types.zip ((argumentValues args Γ a).map Prod.snd) = argumentValues args Γ a := by
    rw [← hc,zipProjections]
  exact MarkedConstructorTupleProof.tupleTags E Γ types _ ht (hl.valid Γ a ha) p (hz.symm ▸ hp)

end LogicLineages.PersistentMarking.ProtectedSpineArgumentProof
