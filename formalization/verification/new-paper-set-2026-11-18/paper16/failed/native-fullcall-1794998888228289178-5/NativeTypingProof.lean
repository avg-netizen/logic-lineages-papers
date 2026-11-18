import LogicLineages.PersistentMarking.NativeOrientationTargets
import LogicLineages.PersistentMarking.ElementaryProof
import LogicLineages.PersistentMarking.TypeSupportFoundationProof
namespace LogicLineages.PersistentMarking.NativeTypingProof
open Spine NativeReduction TypeSupport

theorem appPaper (S : Signature) (σ τ : Ty) (f a : Expr)
    (hf : PaperTerm S f (.arrow σ τ)) (ha : PaperTerm S a σ) : PaperTerm S (app σ τ f a) τ :=
  ⟨.head (.cons hf.1 (.cons ha.1 .nil)),⟨0,rfl⟩,hf.2,ha.2,True.intro⟩
theorem appOrdinary (σ τ : Ty) (f a : Expr) (hf : Ordinary f) (ha : Ordinary a) : Ordinary (app σ τ f a) :=
  ⟨hf,ha,True.intro⟩
theorem markedAppPaper (S : Signature) (σ τ ρ : Ty) (f a : Expr) (extras : Args)
    (hf : PaperTerm S f (.arrow σ τ)) (ha : PaperTerm S a σ)
    (he : ExtrasTyped EmptyContext extras) (hv : ValidArgs S extras) :
    PaperTerm S (.marked (.app σ τ) ρ (.cons f (.cons a .nil)) extras) ρ :=
  ⟨.marked (.cons hf.1 (.cons ha.1 .nil)) he,⟨0,rfl⟩,⟨hf.2,ha.2,True.intro⟩,hv⟩

theorem zeroPaper (S : Signature) : PaperTerm S zero .ground := ⟨.head .nil,⟨1,rfl⟩,True.intro⟩
theorem succConstantPaper (S : Signature) : PaperTerm S (.head .succ .nil) (.arrow .ground .ground) :=
  ⟨.head .nil,⟨1,rfl⟩,True.intro⟩
theorem succPaper (S : Signature) (n : Expr) (hn : PaperTerm S n .ground) : PaperTerm S (succ n) .ground :=
  appPaper S _ _ _ _ (succConstantPaper S) hn

theorem caseConstantPaper (S : Signature) (τ : Ty) :
    PaperTerm S (.head (.case τ) .nil) (.arrow .ground (.arrow τ (.arrow τ τ))) :=
  ⟨.head .nil,⟨1,rfl⟩,True.intro⟩
theorem recConstantPaper (S : Signature) (τ : Ty) :
    PaperTerm S (.head (.recursor τ) .nil) (.arrow .ground (.arrow (stepType τ) (.arrow τ τ))) :=
  ⟨.head .nil,⟨1,rfl⟩,True.intro⟩
theorem rec1Paper (S : Signature) (τ : Ty) (u : Expr) (hu : PaperTerm S u .ground) :
    PaperTerm S (rec1 τ u) (.arrow (stepType τ) (.arrow τ τ)) := appPaper S _ _ _ _ (recConstantPaper S τ) hu
theorem rec2Paper (S : Signature) (τ : Ty) (u A : Expr)
    (hu : PaperTerm S u .ground) (hA : PaperTerm S A (stepType τ)) :
    PaperTerm S (rec2 τ u A) (.arrow τ τ) := appPaper S _ _ _ _ (rec1Paper S τ u hu) hA
theorem recPaper (S : Signature) (τ : Ty) (u A B : Expr)
    (hu : PaperTerm S u .ground) (hA : PaperTerm S A (stepType τ)) (hB : PaperTerm S B τ) :
    PaperTerm S (recTerm τ u A B) τ := appPaper S _ _ _ _ (rec2Paper S τ u A hu hA) hB

theorem leftIncluded (σ τ : Ty) (f a : Expr) : Included f (app σ τ f a) := by
  intro ρ h
  simp only [app,support,supportArgs,List.mem_append]
  exact Or.inr (Or.inl h)
theorem rightIncluded (σ τ : Ty) (f a : Expr) : Included a (app σ τ f a) := by
  intro ρ h
  simp only [app,support,supportArgs,List.mem_append]
  exact Or.inr (Or.inr (Or.inl h))

theorem secondSelect (S : Signature) (σ τ : Ty) (f a : Expr) (extras : Args)
    (hf : PaperTerm S f (.arrow σ τ)) (ha : PaperTerm S a σ) (ho : Ordinary a)
    (he : ExtrasTyped EmptyContext extras) (hv : ValidArgs S extras) :
    Weak S (.marked (.app σ τ) σ (.cons f (.cons a .nil)) extras) a :=
  .select (domains := []) (markedAppPaper S σ τ σ f a extras hf ha he hv) ha
    (Or.inl (.there .here)) ha.1 rfl (ElementaryProof.ordinaryReflexive S a σ ha ho)
end LogicLineages.PersistentMarking.NativeTypingProof
