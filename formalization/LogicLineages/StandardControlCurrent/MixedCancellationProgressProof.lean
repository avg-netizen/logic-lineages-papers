module
public import LogicLineages.StandardControlCurrent.MixedCancellationDefinitions
public import LogicLineages.StandardControlCurrent.MixedCancellationTargets
@[expose] public section
namespace LogicLineages.StandardControlCurrent.MixedCancellation
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm

def weight (xs : List (Int × Summand)) : Nat :=
  (xs.map (fun a => 2+termNodes a.2.term)).sum

private theorem split_weight (xs : List (Int × Summand)) (bs : List Bool)
    (h : bs.length=xs.length) :
    weight ((xs.zip bs).filterMap (fun a => if a.2 then none else some a.1)) +
    weight ((xs.zip bs).filterMap (fun a => if a.2 then some a.1 else none)) = weight xs := by
  induction xs generalizing bs with
  | nil =>
      have hb : bs=[] := by simpa using h
      subst bs
      simp [weight]
  | cons a xs ih =>
      cases bs with
      | nil => simp at h
      | cons b bs =>
          have ht := ih bs (Nat.succ.inj h)
          cases b <;> simp [weight] at * <;> omega

private theorem positive_nodes (r : Row) : termNodes (positiveTerm r)=3+weight r.2 := by
  have hf : ∀ xs : List (Int × Summand),
      termNodes (xs.foldr (fun a rest => Term.add (.multiply a.1.toNat a.2.term) rest) (.numeral 0))
        = 1+weight xs := by
    intro xs
    induction xs with
    | nil => simp [weight,termNodes]
    | cons a xs ih => simp [weight,termNodes,ih] <;> omega
  simp only [positiveTerm,termNodes,hf]
  omega

private theorem negative_nodes (r : Row) : termNodes (negativeTerm r)=3+weight r.2 := by
  have hf : ∀ xs : List (Int × Summand),
      termNodes (xs.foldr (fun a rest => Term.add (.multiply (-a.1).toNat a.2.term) rest) (.numeral 0))
        = 1+weight xs := by
    intro xs
    induction xs with
    | nil => simp [weight,termNodes]
    | cons a xs ih => simp [weight,termNodes,ih] <;> omega
  simp only [negativeTerm,termNodes,hf]
  omega

private theorem atom_decrease (a : Atom) (bs : List Bool) (he : enabled a.row bs=true) :
    matrixNodes (replaceRow a (retained a.row bs)).compile < matrixNodes a.compile := by
  have hh := he
  simp only [enabled,Bool.and_eq_true,beq_iff_eq] at hh
  have hn : selected a.row bs ≠ [] := by
    intro hz
    simpa [hz] using hh.2
  have hp : 0 < weight (selected a.row bs) := by
    cases hs : selected a.row bs with
    | nil => exact False.elim (hn hs)
    | cons b xs => simp [weight] <;> omega
  have hw := split_weight a.row.2 bs hh.1.1
  change weight (retained a.row bs).2 + weight (selected a.row bs)=weight a.row.2 at hw
  have hlt : weight (retained a.row bs).2 < weight a.row.2 := by omega
  cases a <;> simp only [replaceRow,Atom.compile,atMost,matrixNodes,absoluteTerm,termNodes,
    positive_nodes,negative_nodes,Atom.row] at * <;> omega

theorem context_nodes (c : Context) (p q : Matrix) (h : matrixNodes p < matrixNodes q) :
    matrixNodes (c.plug p) < matrixNodes (c.plug q) := by
  induction c <;> simp only [Context.plug,matrixNodes] at * <;> omega

theorem progress : MixedCancellationTargets.Progress := by
  intro c a bs
  by_cases he : enabled a.row bs=true
  · have ha := atom_decrease a bs he
    have hh : matrixNodes (.conjunction (domainFormula a.row).compile
        (replaceRow a (retained a.row bs)).compile) < matrixNodes (guardedAtom a).compile := by
      simp only [guardedAtom,Formula.compile,matrixNodes]
      omega
    have hc := context_nodes c _ _ hh
    simp only [step,he,if_true,rewritten,before,matrixNodes]
    exact ⟨fun _ => by omega,by simp,by simp⟩
  · simp [step,he]
end LogicLineages.StandardControlCurrent.MixedCancellation
