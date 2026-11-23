module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationTypingProof
public import LogicLineages.NativeModule.PersistentMarking.DecisionInventoryProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRealizationWindowProof
open Spine NumberedWindowSyntax NumberedWindowTupleTargets NumberedWindowRealizationShapeProof
open DecisionInventory

def DeclaredTerm (S : Signature) (q : Expr) : Prop :=
  Valid S q → ∀ f, f ∈ heads q → Admitted S f

private def DeclaredArgs (S : Signature) (args : Spine.Args) : Prop :=
  ValidArgs S args → ∀ f, f ∈ headsArgs args → Admitted S f

theorem admitted (S : Signature) (q : Expr) : DeclaredTerm S q := by
  apply @Expr.rec (DeclaredTerm S) (DeclaredArgs S)
  · intro σ x _ f h
    cases h
  · intro σ i _ f h
    cases h
  · intro σ q h; exact h
  · intro f bs hb h g hg
    rcases List.mem_cons.mp hg with he | he
    · rw [he]; exact h.1
    · exact hb h.2 g he
  · intro f τ bs es hb he h g hg
    rcases List.mem_cons.mp hg with hg | hg
    · rw [hg]; exact h.1
    · rcases List.mem_append.mp hg with hg | hg
      · exact hb h.2.1 g hg
      · exact he h.2.2 g hg
  · intro _ g h
    cases h
  · intro q args hq ha h f hf
    rcases List.mem_append.mp hf with hf | hf
    · exact hq h.1 f hf
    · exact ha h.2 f hf

theorem inWindow : RealizationInWindow := by
  intro S K C σ n q Q hTyped hValid hAdmissible hRealizes
  have hshape := termShape hRealizes
  refine ⟨NumberedWindowRealizationTypingProof.typed hRealizes C σ hTyped,?_,?_⟩
  · intro τ ht
    rw [hshape.2.1] at ht
    exact hAdmissible τ ht
  · intro f hf
    rw [hshape.2.2] at hf
    exact ⟨admitted S q hValid f hf,
      fun τ ht => hAdmissible τ (DecisionInventoryProof.declarations q f hf τ ht)⟩

end LogicLineages.PersistentMarking.NumberedWindowRealizationWindowProof
