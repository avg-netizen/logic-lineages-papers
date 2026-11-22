# Paper 17 ordinary value operand residues

The source table is in Paper 17 `sections/controls.tex` lines 206–220.
The shared residue requirement is in `sections/arithmetic.tex` lines 231–240.
At the original raw input x, write j for x modulo 2m. The operand compiler
retains j for identity, uses 2 floor(j/2) minus 2a for a positive bare
iterate, uses 2 floor(j/2) minus 2(k+a) for a short proper entry, and
uses 2 ceil(N(mu)/2) minus 2a for the other proper entries. All differences
are signed, and the outer iterate a stays in each entry branch.

The exact code proof supplies primitive recursive literal field dispatch and
tail calculation on all raw inputs. It proves canonical calibration at each
original ValueField code. The actual proof applies the original bare and
derived entry tables, uses the required selected control and source tails,
and transports the signed residue to j. It obtains one actual lower-operand
value, including its original domain and closed read at the same ρ(rank).
Identity requires no tail. A positive bare iterate requires max(m,B). Each
proper entry uses the full original tail max(N(lambda), N(mu)+3, m, B).

The exported scope covers ordinary values. Count residues, optional explicit
half-fields, complete mixed formula compilation, unprepared strip coverage
and the printed #704 qualification have their own obligations.
