module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalLambdaShapeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalNeutralEdgesProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalLambdaApplicationEdgesProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowSimulationData
open NumberedWindowPrimary NumberedWindowExternalApplication NumberedWindowExternalLambda
open NumberedWindowExternalSubstitutionTargets NumberedWindowExternalLambdaEdgesTargets
open NumberedWindowExternalNeutralPrimaryProof
open NumberedWindowPreservationGuardProof (appParts lamBody)

private theorem rawApp {S K σ τ q u out} (h : RawStep S K (.auxApp σ τ q u) out) :
    out = .bottom τ ∨ (∃ value, q = .lam σ value ∧ out = substitute (.cons u .nil) 0 value) ∨
      ∃ r, RawStep S K q r ∧ out = .auxApp σ τ r u := by
  cases h with
  | beta => exact .inr (.inl ⟨_,rfl,rfl⟩)
  | bottom _ => exact .inl rfl
  | auxFunction h => exact .inr (.inr ⟨_,h,rfl⟩)

theorem applied : LambdaApplicationEdges := by
  intro S K C σ τ hk hτ v u out
  refine Quot.inductionOn v ?_
  intro V
  refine Quot.inductionOn u ?_
  intro U step
  obtain ⟨a,b,ea,eb,raw⟩ := step
  let f := lamCarrier hk hτ V
  have equiv := primaryOfClassEquality (appCarrier hk f U) a ea.symm
  obtain ⟨g,arg,ha,ef,eu⟩ := applicationComponents S K C σ τ f.val U.val a.val equiv
  have parts := appParts (show InWindow S K C τ (.auxApp σ τ g arg) from ha ▸ a.property)
  let G : WindowCarrier S K C (.arrow σ τ) := ⟨g,parts.1⟩
  let A : WindowCarrier S K C σ := ⟨arg,parts.2⟩
  have hG : classOf G = classOf f := Quot.sound ef.symm
  have hA : classOf A = classOf U := Quot.sound eu.symm
  have s : RawStep S K (.auxApp σ τ g arg) b.val := ha ▸ raw
  rcases rawApp s with bot | ⟨body,hg,hs⟩ | ⟨r,hr,hb⟩
  · exact .inl ⟨b,bot,eb⟩
  · have wb : InWindow S K (C.push σ) τ body := lamBody (hg ▸ parts.1)
    let B : WindowCarrier S K (C.push σ) τ := ⟨body,wb⟩
    obtain ⟨w,hw,bodyEq⟩ := NumberedWindowExternalLambdaShapeProof.components
      S K C σ τ V.val g ef
    have ew : w = body := (NTerm.lam.inj (hw.symm.trans hg)).2
    subst w
    have eqB : classOf B = classOf V := Quot.sound bodyEq.symm
    have actual : b = bodyInstance hk B A := Subtype.ext hs
    exact .inr (.inr (.inr ⟨B,A,eqB,hA,eb.symm.trans (congrArg classOf actual)⟩))
  · have wr := appParts (show InWindow S K C τ (.auxApp σ τ r arg) from hb ▸ b.property)
    let R : WindowCarrier S K C (.arrow σ τ) := ⟨r,wr.1⟩
    have fnStep : ClassEdge (lamClass hk hτ (classOf V)) (classOf R) := ⟨G,R,hG,rfl,hr⟩
    have literal : b = appCarrier hk R A := Subtype.ext hb
    have outEq : out = appClass hk (classOf R) (classOf U) := by
      calc
        out = classOf b := eb.symm
        _ = classOf (appCarrier hk R A) := congrArg classOf literal
        _ = appClass hk (classOf R) (classOf A) := rfl
        _ = appClass hk (classOf R) (classOf U) := congrArg (appClass hk (classOf R)) hA
    rcases NumberedWindowExternalLambdaShapeProof.edges S K C σ τ hk hτ (classOf V)
      (classOf R) fnStep with bottom | ⟨w,p,e⟩
    · exact .inr (.inl ⟨_,bottom,outEq⟩)
    · exact .inr (.inr (.inl ⟨w,p,outEq.trans (congrArg (fun z => appClass hk z (classOf U)) e)⟩))

end LogicLineages.PersistentMarking.NumberedWindowExternalLambdaApplicationEdgesProof
