# Additional example: identical growth multipliers, different full spectra

This example was removed from the main narrative. Its original proof is
preserved in `spectral-perturbation.tex`; the construction uses the base-19
allocation from `../../section5/certificates/n424/`.

From the repository root run:

```sh
python supplementary/additional/spectrum/verify_spectral.py
```

The checker verifies the four signed allocation changes, their capacity margin,
the rank-one mass correction annihilating (55,23), the strict trace-sign
calculation, and the small noncommuting witness. It writes
`spectral-verification.json`. The underlying base allocation was checked by
the independent Section 5 verifier; run that verifier too for the full
dependency chain. Only the relative path to that input was changed on relocation.

This is an additional computer-assisted example, not a new Lean formalisation
claim. Use Python 3.11 or later without `-O` or `-OO`; no external packages.
The preserved proof is a LaTeX fragment using manuscript notation.
