module
public import LogicLineages.PermittedControl.ActualFullValueMaximalMetadataTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ActualFullValueMaximalMetadata
open ActualFullValueLabels (Label ActualLabel)
open ActualFullLabelPairGuards (Pair Answer ActualOutcome)
open ActualFiniteFullValueGuards (pairs Matches)

private theorem compareCode (u v : Nat) : (compare u v).code = numericalComparison u v := by
  by_cases lt : u < v
  · simp [compare,numericalComparison,Answer.code,lt]
  · by_cases eq : u = v <;> simp [compare,numericalComparison,Answer.code,lt,eq]

private theorem answerInjective : Function.Injective Answer.code := by
  intro a b h
  cases a <;> cases b <;> simp_all [Answer.code]

private theorem literalReadUnique (f θ : Nat → Nat) (l : Label) (x y : Nat)
    (a : ActualLabel f θ l x) (b : ActualLabel f θ l y) : x = y :=
  Option.some.inj (Option.some.inj (a.2.2.symm.trans b.2.2))

private theorem outcomeUnique (f θ : Nat → Nat) (p : Pair) (a b : Answer)
    (first : ActualOutcome f θ p a) (second : ActualOutcome f θ p b) : a = b := by
  obtain ⟨u,v,hu,hv,eq⟩ := first
  obtain ⟨u',v',hu',hv',eq'⟩ := second
  apply answerInjective
  exact eq.symm.trans ((congrArg₂ numericalComparison
    (literalReadUnique f θ p.1 u u' hu hu') (literalReadUnique f θ p.2 v v' hv hv')).trans eq')

private theorem uniqueVector (f θ : Nat → Nat) (ps : List Pair) (as bs : List Answer)
    (left : Matches f θ ps as) (right : Matches f θ ps bs) : as = bs := by
  induction left generalizing bs with
  | nil =>
      cases right
      rfl
  | @cons p a ps as hp _ next =>
      cases right with
      | cons h t =>
          exact congrArg₂ List.cons (outcomeUnique f θ p _ _ hp h) (next _ t)

private theorem matchedRow (f θ : Nat → Nat) (l : Label) (u : Nat) (first : ActualLabel f θ l u)
    {ls : List Label} {vs : List Nat} (aligned : List.Forall₂ (ActualLabel f θ) ls vs) :
    Matches f θ (ls.map (fun r => (l,r))) (vs.map (compare u)) := by
  induction aligned with
  | nil => exact .nil
  | @cons r v ls vs h _ next =>
      exact .cons ⟨u,v,first,h,(compareCode u v).symm⟩ next

private theorem appendMatched (f θ : Nat → Nat) {ps qs : List Pair} {as bs : List Answer}
    (first : Matches f θ ps as) (second : Matches f θ qs bs) :
    Matches f θ (ps ++ qs) (as ++ bs) := by
  induction first with
  | nil => exact second
  | cons head _ next => exact .cons head next

private theorem matchedBlocks (f θ : Nat → Nat)
    {ls : List Label} {vs : List Nat} (aligned : List.Forall₂ (ActualLabel f θ) ls vs)
    {all : List Label} {ws : List Nat} (allRead : List.Forall₂ (ActualLabel f θ) all ws) :
    Matches f θ (ls.flatMap (fun l => all.map (fun r => (l,r))))
      (vs.flatMap (fun u => ws.map (compare u))) := by
  induction aligned with
  | nil => exact .nil
  | @cons l u ls vs head _ tail =>
      exact appendMatched f θ (matchedRow f θ l u head allRead) tail

theorem exactMatchedNumericVector : ExactMatchedNumericVector := by
  intro f θ ls vs aligned as
  have canonical : Matches f θ (pairs ls) (numericVector vs) :=
    matchedBlocks f θ aligned aligned
  exact ⟨fun actual => uniqueVector f θ _ as _ actual canonical,
    fun same => same.symm ▸ canonical⟩

end LogicLineages.PermittedControl.ActualFullValueMaximalMetadata
