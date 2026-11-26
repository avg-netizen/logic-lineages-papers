# Supporting inverse-cut scope

Dependency toward current m:thm:snyatkov, not a numbered source theorem. Actual Snyatkov2008 p40 total inverse conventions and pp50–51 inverse boundary witnesses motivate this exact arithmetic step. No general elimination claim.

Input is the right-nested tuple(a,b,lo,hi,m,r). Cut is genuine exists x:Nat with a<=x<=b,lo<=g(x)<=hi,x%m=r. answer explicitly rejects m=0 and r>=m, then tests the concrete least admissible candidate against b and hi. All parameters vary jointly; no parameter valuation is frozen or independently renamed. ActualLowerCuts separately handles g=Phi and actual fixed-seed H below first range values, and LeastResidue proves the candidate rather than assuming a witness. ActualPrograms requires genuine PR of all concrete programs, including malformed inputs. Empty intervals and modulus1 are included. No tail assumption, positivity restriction on raw bounds or inverse oracle.

This pays only this nonlinear interval/residue cut. Expanded formula substitution, capture/shadowing, arbitrary sums of nonlinear terms, negated branches and full alternation remain unpaid. Existing inverse graph/order/PR proofs are reusable only after actual function matching and fresh recursive evidence.
