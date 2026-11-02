module
public import LogicLineages.OrdinalComparison.SourceReserveLowerBoundPositiveProof
public import LogicLineages.OrdinalComparison.SourceAssignmentSupportStructureProof
public import LogicLineages.OrdinalComparison.HeadFiniteSurplusProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
open ScalarCarrierAccounting ActiveScalarAnnotation AssignmentSupport AssignmentSupport.Proof
open AdmissibleSum

theorem reserve_add (xs ys : List Carrier) (c d : Nat) :
    reserve (xs++ys) (c+d+1) = reserve xs c + reserve ys d + 1 := by
  simp only [reserve, List.length_append, Nat.cast_add, Nat.cast_one]
  omega

private theorem replicate_flatten_succ (xs : List Carrier) (n : Nat) :
    (List.replicate (n+1) xs).flatten = (List.replicate n xs).flatten ++ xs := by
  rw [List.replicate_add, List.flatten_append]
  simp

private theorem left_repeated_account {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List Carrier) (c : Nat)
    (hac : Account q xs c) (ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q)
    (n : Nat) :
    ∃ d : Nat,
      Account (expand (OrdinalSyntax.leftShape n) (fun _ => q)) (List.replicate (n+1) xs).flatten d ∧
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
        (expand (OrdinalSyntax.leftShape n) (fun _ => q)) ∧
      reserve (List.replicate (n+1) xs).flatten d = ((n+1 : Nat) : Int)*reserve xs c+(n : Int) := by
  induction n with
  | zero =>
    refine ⟨c,?_,?_,?_⟩
    · simpa [OrdinalSyntax.leftShape,expand] using hac
    · exact ha
    · simp
  | succ n ih =>
    obtain ⟨d,hd,hactive,hreserve⟩ := ih
    have hactive' : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
        (.add (expand (OrdinalSyntax.leftShape n) (fun _ => q)) q) := by
      change _ ∈ names (.add _ q)
      rw [names_add,List.mem_append]
      exact Or.inr ha
    refine ⟨d+c+1,?_,?_,?_⟩
    · rw [replicate_flatten_succ]
      exact .add hactive' hd hac
    · exact hactive'
    · rw [replicate_flatten_succ,reserve_add,hreserve]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

/-- The list consists of exactly n copies of the original occurrence list,
retaining actual labels, their order, and all repeated occurrences. -/
theorem repeated_account_exact {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List Carrier) (c : Nat)
    (hac : Account q xs c) (ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q)
    (n : Nat) (hn : 0 < n) :
    ∃ d : Nat,
      Account (AdmissibleAssignment.repeated OrdinalSyntax.defaultPolicy .scalarRepeat n q)
        (List.replicate n xs).flatten d ∧
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
        (AdmissibleAssignment.repeated OrdinalSyntax.defaultPolicy .scalarRepeat n q) ∧
      reserve (List.replicate n xs).flatten d = (n : Int)*reserve xs c+((n : Int)-1) := by
  cases n with
  | zero => omega
  | succ n =>
    obtain ⟨d,hd,ha',he⟩ := left_repeated_account q xs c hac ha n
    refine ⟨d,?_,?_,?_⟩
    · exact hd
    · exact ha'
    · simpa only [Nat.cast_add,Nat.cast_one,add_sub_cancel_right] using he

theorem repeated_account {k Γ}
    (q : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) (xs : List Carrier) (c : Nat)
    (hac : Account q xs c) (ha : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) q)
    (n : Nat) (hn : 0 < n) :
    ∃ (ys : List Carrier) (d : Nat),
      Account (AdmissibleAssignment.repeated OrdinalSyntax.defaultPolicy .scalarRepeat n q) ys d ∧
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _)
        (AdmissibleAssignment.repeated OrdinalSyntax.defaultPolicy .scalarRepeat n q) ∧
      reserve ys d = (n : Int)*reserve xs c+((n : Int)-1) := by
  obtain ⟨d,hd,ha',he⟩ := repeated_account_exact q xs c hac ha n hn
  exact ⟨(List.replicate n xs).flatten,d,hd,ha',he⟩

theorem application_bound {k Γ}
    (h a b : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (ht : AdditiveHeadTree.HeadTree (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) h)
    (hcollapse : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.collapse h (.add a b)))
    (htail : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) (.add a b))
    (A B : Int) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (boundA : ∀ xs c, Account a xs c → A ≤ reserve xs c)
    (boundB : ∀ xs c, Account b xs c → B ≤ reserve xs c)
    (nonfiniteSum : Ordinal.omega0 ≤ unitValue h → 5 ≤ A+B)
    (xs : List Carrier) (c : Nat) (hac : Account (.collapse h (.add a b)) xs c) :
    (4 : Int) ≤ reserve xs c := by
  cases hac with
  | free hn => exact False.elim (hn hcollapse)
  | @finite _ _ xs ct n active hfinite tail =>
    have hp := positiveHeadValue _ 1 h (by decide) (AdditiveHeadTree.Proof.head_grade ht)
    rw [hfinite] at hp
    have hn : 1 ≤ n := by exact_mod_cast hp
    cases tail with
    | free hinactive => exact False.elim (hinactive htail)
    | @add _ _ xs ys ca cb active aca acb =>
      have ha := boundA xs ca aca
      have hb := boundB ys cb acb
      have he : reserve (xs++ys) (ca+cb+1+n+HeadFiniteSurplus.surplus h) =
          reserve xs ca + reserve ys cb + 1 + (n : Int) + (HeadFiniteSurplus.surplus h : Int) := by
        simp only [reserve,List.length_append,Nat.cast_add,Nat.cast_one]
        omega
      rw [he]
      have hn' : (1 : Int) ≤ (n : Int) := by exact_mod_cast hn
      omega
  | @nonfinite _ _ xs ct label active hnonfinite hlabel tail =>
    have hsum := nonfiniteSum hnonfinite
    have hδ : 1 ≤ HeadFiniteSurplus.surplus h := by
      apply (HeadFiniteSurplus.Proof.surplusBounds k Γ h ht).2.2 (fun _ => 1)
      rw [HeadFiniteSurplus.Proof.headClosure_units]
      exact hnonfinite
    cases tail with
    | free hinactive => exact False.elim (hinactive htail)
    | @add _ _ xs ys ca cb active aca acb =>
      have ha := boundA xs ca aca
      have hb := boundB ys cb acb
      have he : reserve ((xs++ys)++[label]) (ca+cb+1+HeadFiniteSurplus.surplus h) =
          reserve xs ca + reserve ys cb + 1 + (HeadFiniteSurplus.surplus h : Int) - 3 := by
        simp only [reserve,List.length_append,List.length_singleton,Nat.cast_add,Nat.cast_one]
        omega
      rw [he]
      have hδ' : (1 : Int) ≤ (HeadFiniteSurplus.surplus h : Int) := by exact_mod_cast hδ
      omega

end LogicLineages.OrdinalComparison.Source.SourceReserveLowerBound.Proof
