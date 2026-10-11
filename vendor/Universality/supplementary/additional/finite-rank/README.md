# Historical finite-rank argument and its finite constant checks

This folder preserves material omitted from the current manuscript. The old
argument is in `historical-finite-rank-argument.tex`, a LaTeX fragment using
manuscript macros and references. Its inclusion here is archival: the upload
does not re-establish or independently audit the full uniform-realisation lemma
or the arbitrary-finite-rank theorem.

From the repository root run:

```sh
python supplementary/additional/finite-rank/verify_rank_constants.py
```

The checker uses exact rational intervals with integer square-root enclosures
for the finite inequalities, together with exact matrix, divisibility and
minor-gcd checks. It writes `verify_rank_constants.json`. Decimal interval
endpoints in that output are for display; the assertions use exact arithmetic.

**Passing these finite checks is not a verification of the full asymptotic
realisation argument.** This file is not needed for the two principal Section 5
conclusions currently retained in the paper. The script is unchanged from the
manuscript repository. Use Python 3.11 or later without optimization flags;
only the standard library is required.
